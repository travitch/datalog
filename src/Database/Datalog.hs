{-# LANGUAGE FlexibleContexts #-}
module Database.Datalog (
  -- * Types
  Database,
  Relation,
  DatabaseBuilder,
  QueryBuilder,
  Predicate,
  Clause(..),
  Literal(..),
  QueryPlan,

  -- * Building the IDB
  makeDatabase,
  addRelation,
  assertFact,

  -- * Building Logic Programs
  (|-),
  assertRule,
  relationPredicateFromName,
  inferencePredicate,
  issueQuery,

  -- * Evaluating Queries
  queryDatabase,
  buildQueryPlan,
  executeQueryPlan
  ) where

import Control.Failure
import Control.Monad ( foldM )
import Data.Hashable
import Data.Text ( Text )

import Database.Datalog.Database
import Database.Datalog.Errors
import Database.Datalog.Rules
import Database.Datalog.MagicSets
import Database.Datalog.Stratification

-- FIXME: Unify predicate and relation for simplicity, also remove the
-- distinction between IDB and EDB predicates


-- | A fully-stratified query plan that is ready to be executed.
data QueryPlan a = QueryPlan (Query a) [[Rule a]]

-- | This is a shortcut to build a query plan and execute in one step,
-- with no bindings provided.  It doesn't make sense to have bindings
-- in one-shot queries.
queryDatabase :: (Failure DatalogError m, Eq a, Hashable a)
                 => Database a -- ^ The intensional database of facts
                 -> QueryBuilder m a (Query a) -- ^ A monad building up a set of rules and returning a Query
                 -> m [[a]]
queryDatabase idb qm = do
  qp <- buildQueryPlan idb qm
  executeQueryPlan qp idb []

-- | Given a query description, build a query plan by stratifying the
-- rules and performing the magic sets transformation.  Throws an
-- error if the rules cannot be stratified.
buildQueryPlan :: (Failure DatalogError m, Eq a, Hashable a)
                  => Database a
                  -> QueryBuilder m a (Query a)
                  -> m (QueryPlan a)
buildQueryPlan idb qm = do
  let ipreds = databasePredicates idb
  (q, rs) <- runQuery qm idb
  rs' <- magicSetsRules ipreds q rs
  strata <- stratifyRules rs'
  return $! QueryPlan q strata

-- | Execute a query plan with an intensional database and a set of
-- bindings (substituted in for 'BindVar's).  Throw an error if:
--
--  * The rules and database define the same relation
executeQueryPlan :: (Failure DatalogError m, Eq a, Hashable a)
                    => QueryPlan a -> Database a -> [(Text, a)] -> m [[a]]
executeQueryPlan (QueryPlan q strata) idb bindings = do
  -- FIXME: Bindings is used to substitute in values for BoundVars in
  -- the query.  Those might actually affect the magic rules that are
  -- required...
  edb <- executePlan' strata idb
  let pt = queryToPartialTuple q
      p = queryPredicate q
  return $! map unTuple $ select edb p pt

-- Private helpers

-- | Execute the query plan until no new facts are added to the database
executePlan' :: (Failure DatalogError m, Eq a, Hashable a)
                => [[Rule a]] -> Database a -> m (Database a)
executePlan' strata db = do
  db' <- applyStrata strata db
  case databasesDiffer db db' of
    True -> executePlan' strata db'
    False -> return db'

-- | Apply the rules in each stratum bottom-up.  Stop at a stratum if
-- nothing changes (since no new facts can be added in later stages if
-- nothing changed in a lower stage)
applyStrata :: (Failure DatalogError m, Eq a, Hashable a)
               => [[Rule a]] -> Database a -> m (Database a)
applyStrata [] db = return db
applyStrata (s:strata) db = do
  db' <- foldM applyRule db s
  case databasesDiffer db db' of
    True -> applyStrata strata db'
    False -> return db
