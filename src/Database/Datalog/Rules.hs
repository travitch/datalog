{-# LANGUAGE FlexibleContexts #-}
module Database.Datalog.Rules (
  Term(..),
  Clause(..),
  Rule(..),
  Query,
  QueryMonad,
  QueryState(..),
  BodyClause(..),
  (|-),
  assertRule,
  relationPredicateFromName,
  rulePredicates
  ) where

import Control.Failure
import Control.Monad.State.Strict
import Data.Maybe ( mapMaybe )
import Data.Text ( Text )

import Database.Datalog.Errors
import Database.Datalog.Database

data Term a = LogicVar !Text
              -- ^ A basic logic variable.  Equality is based on the
              -- variable name.
            | BindVar !Text
              -- ^ A special variable available in queries that can be
              -- bound at query execution time
            | Literal a
              -- ^ A user-provided literal from the domain a

data Clause a = Clause { clausePredicate :: Predicate
                       , clauseTerms :: [Term a]
                       }

-- | Body clauses can be normal clauses, negated clauses, or
-- conditionals.  Conditionals are arbitrary-arity (via a list)
-- functions over literals and logic variables.
data BodyClause a = BodyClause (Clause a)
                  | NegatedClause (Clause a)
                  | ConditionalClause ([a] -> Bool) [Term a]

-- | A rule has a head and body clauses.  Body clauses can be normal
-- clauses, negated clauses, or conditionals.
data Rule a = Rule { ruleHead :: Clause a
                   , ruleBody :: [BodyClause a]
                   }

bodyClausePredicate :: BodyClause a -> Maybe Predicate
bodyClausePredicate bc =
  case bc of
    BodyClause c -> Just $ clausePredicate c
    NegatedClause c -> Just $ clausePredicate c
    _ -> Nothing

rulePredicates :: Rule a -> [Predicate]
rulePredicates (Rule h bcs) = clausePredicate h : mapMaybe bodyClausePredicate bcs

newtype Query a = Query { unQuery :: Clause a }

infixr 0 |-

-- | Assert a rule
(|-) :: (Failure DatalogError m) => Clause a -> [BodyClause a] -> QueryMonad m a ()
(|-) = assertRule

assertRule :: (Failure DatalogError m) => Clause a -> [BodyClause a] -> QueryMonad m a ()
assertRule h b = do
  s <- get
  put s { queryRules = Rule h b : queryRules s }



-- | Retrieve a Relation handle from the IDB.  If the Relation does
-- not exist, an error will be raised.
relationPredicateFromName :: (Failure DatalogError m)
                             => Text -> QueryMonad m a Predicate
relationPredicateFromName name = do
  idb <- gets intensionalDatabase
  case RelationPredicate (Relation name) `elem` databasePredicates idb of
    False -> lift $ failure (NoRelationError name)
    True -> return $! (RelationPredicate (Relation name))

inferencePredicate :: (Failure DatalogError m)
                      => Text -> QueryMonad m a Predicate
inferencePredicate = return . InferencePredicate


data QueryState a = QueryState { intensionalDatabase :: Database a
                               , queryRules :: [Rule a]
                               }
type QueryMonad m a = StateT (QueryState a) m