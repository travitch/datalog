{-# LANGUAGE FlexibleContexts #-}
module Database.Datalog.Rules (
  Adornment(..),
  Term(..),
  Clause(..),
  AdornedClause(..),
  Rule(..),
  Literal(..),
  Query,
  QueryMonad,
  (|-),
  assertRule,
  relationPredicateFromName,
  rulePredicates,
  runQuery
  ) where

import Control.Failure
import Control.Monad.State.Strict
import Data.HashSet ( HashSet )
import qualified Data.HashSet as HS
import Data.Maybe ( mapMaybe )
import Data.Monoid
import Data.Text ( Text )

import Database.Datalog.Errors
import Database.Datalog.Database


data QueryState a = QueryState { intensionalDatabase :: Database a
                               , queryRules :: [(Clause a, [Literal Clause a])]
                               }

-- | The Monad in which queries are constructed and rules are declared
type QueryMonad m a = StateT (QueryState a) m


data Term a = LogicVar !Text
              -- ^ A basic logic variable.  Equality is based on the
              -- variable name.
            | BindVar !Text
              -- ^ A special variable available in queries that can be
              -- bound at query execution time
            | Atom a
              -- ^ A user-provided literal from the domain a

data Clause a = Clause { clausePredicate :: Predicate
                       , clauseTerms :: [Term a]
                       }

data Adornment = Free | Bound

data AdornedClause a = AdornedClause { adornedClausePredicate :: Predicate
                                     , adornedClauseTerms :: [(Term a, Adornment)]
                                     }

-- | Body clauses can be normal clauses, negated clauses, or
-- conditionals.  Conditionals are arbitrary-arity (via a list)
-- functions over literals and logic variables.
data Literal ctype a = Literal (ctype a)
                     | NegatedLiteral (ctype a)
                     | ConditionalClause ([a] -> Bool) [Term a]

-- | A rule has a head and body clauses.  Body clauses can be normal
-- clauses, negated clauses, or conditionals.
data Rule a = Rule { ruleHead :: AdornedClause a
                   , ruleBody :: [Literal AdornedClause a]
                   }

newtype Query a = Query { unQuery :: Clause a }

infixr 0 |-

-- | Assert a rule
(|-) :: (Failure DatalogError m) => Clause a -> [Literal Clause a] -> QueryMonad m a ()
(|-) = assertRule

assertRule :: (Failure DatalogError m) => Clause a -> [Literal Clause a] -> QueryMonad m a ()
assertRule h b = do
  s <- get
  put s { queryRules = (h, b) : queryRules s }

adornLiteral :: Literal Clause a
                -> ([Literal AdornedClause a], HashSet (Term a))
                -> ([Literal AdornedClause a], HashSet (Term a))
adornLiteral = undefined

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



literalClausePredicate :: Literal AdornedClause a -> Maybe Predicate
literalClausePredicate bc =
  case bc of
    Literal c -> Just $ adornedClausePredicate c
    NegatedLiteral c -> Just $ adornedClausePredicate c
    _ -> Nothing

rulePredicates :: Rule a -> [Predicate]
rulePredicates (Rule h bcs) = adornedClausePredicate h : mapMaybe literalClausePredicate bcs

adornRules :: (Failure DatalogError m)
              => Query a -> [(Clause a, [Literal Clause a])] -> m [Rule a]
adornRules = undefined

-- | Run the QueryMonad action to build a query and initial rule
-- database
--
-- Rules are adorned (marking each variable as Free or Bound as they
-- appear) before being returned.
runQuery :: (Failure DatalogError m)
            => QueryMonad m a (Query a) -> Database a -> m (Query a, [Rule a])
runQuery qm idb = do
  (q, QueryState _ rs) <- runStateT qm (QueryState idb [])
  rs' <- adornRules q rs
  return (q, rs')