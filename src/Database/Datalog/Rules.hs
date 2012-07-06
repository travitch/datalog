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
  issueQuery,
  runQuery
  ) where

import Control.Failure
import Control.Monad.State.Strict
import Data.Hashable
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

instance (Hashable a) => Hashable (Term a) where
  hash (LogicVar t) = hash t `combine` 1
  hash (BindVar t) = hash t `combine` 2
  hash (Atom a) = hash a

instance (Eq a) => Eq (Term a) where
  (LogicVar t1) == (LogicVar t2) = t1 == t2
  (BindVar t1) == (BindVar t2) = t1 == t2
  (Atom a1) == (Atom a2) = a1 == a2
  _ == _ = False

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

newtype Query a = Query { unQuery :: AdornedClause a }

infixr 0 |-

-- | Assert a rule
(|-) :: (Failure DatalogError m) => Clause a -> [Literal Clause a] -> QueryMonad m a ()
(|-) = assertRule

assertRule :: (Failure DatalogError m) => Clause a -> [Literal Clause a] -> QueryMonad m a ()
assertRule h b = do
  s <- get
  put s { queryRules = (h, b) : queryRules s }

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

issueQuery :: (Failure DatalogError m) => Clause a -> m (Query a)
issueQuery = return . adornQuery

-- If the query has a bound literal, that influences the rules it
-- corresponds to.  Other rules are not affected.  Those positions
-- bound in the query are bound in the associated rules.
--
-- Note: all variables in the head must appear in the body
adornRule :: (Failure DatalogError m, Eq a, Hashable a)
              => Query a -> (Clause a, [Literal Clause a]) -> m (Rule a)
adornRule q (hd, lits) = do
  (vmap, Literal hd') <- adornLiteral mempty (Literal hd)
  (_, lits') <- mapAccumM adornLiteral vmap lits
  return $! Rule hd' lits'

adornQuery :: Clause a -> Query a
adornQuery (Clause p ts) = Query $ AdornedClause p $ map adorn ts
  where
    adorn t@(LogicVar _) = (t, Free)
    -- BoundVars will become bound by the time this matters
    adorn t = (t, Bound)

adornLiteral :: (Failure DatalogError m, Eq a, Hashable a)
                => HashSet (Term a)
                -> Literal Clause a
                -> m (HashSet (Term a), Literal AdornedClause a)
adornLiteral boundVars lit =
  case lit of
    Literal c -> adornClause Literal c
    NegatedLiteral c -> adornClause NegatedLiteral c
    ConditionalClause f ts -> return (boundVars, ConditionalClause f ts)
  where
    adornClause constructor (Clause p ts) = do
      (bound', ts') <- mapAccumM adornTerm boundVars ts
      let c' = constructor $ AdornedClause p ts'
      return (bound', c')
    adornTerm bvs t =
      case t of
        -- Atoms are always bound
        Atom _ -> return (bvs, (t, Bound))
        BindVar _ -> error "Bind variables are only allowed in queries"
        LogicVar _ ->
          -- The first occurrence is Free, while the rest are Bound
          case HS.member t bvs of
            True -> return (bvs, (t, Bound))
            False -> return (HS.insert t bvs, (t, Free))

-- | Run the QueryMonad action to build a query and initial rule
-- database
--
-- Rules are adorned (marking each variable as Free or Bound as they
-- appear) before being returned.
runQuery :: (Failure DatalogError m, Eq a, Hashable a)
            => QueryMonad m a (Query a) -> Database a -> m (Query a, [Rule a])
runQuery qm idb = do
  (q, QueryState _ rs) <- runStateT qm (QueryState idb [])
  rs' <- mapM (adornRule q) rs
  return (q, rs')


mapAccumM :: (Monad m, MonadPlus p) => (acc -> x -> m (acc, y)) -> acc -> [x] -> m (acc, p y)
mapAccumM _ z [] = return (z, mzero)
mapAccumM f z (x:xs) = do
  (z', y) <- f z x
  (z'', ys) <- mapAccumM f z' xs
  return (z'', return y `mplus` ys)
