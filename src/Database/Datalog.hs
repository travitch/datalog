{-# LANGUAGE FlexibleContexts #-}
module Database.Datalog (
  -- * Types
  Database,
  Relation,
  DatabaseBuilder,
  QueryBuilder,
  Term(..),
  QueryPlan,
  DatalogError(..),
  Query,
  Failure,

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
  lit,
  negLit,
  cond1,
  cond2,
  cond3,
  cond4,
  cond5,

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
import Database.Datalog.Evaluate
import Database.Datalog.Rules
import Database.Datalog.MagicSets
import Database.Datalog.Stratification

import Debug.Trace
debug = flip trace

-- | A fully-stratified query plan that is ready to be executed.
data QueryPlan a = QueryPlan (Query a) [[Rule a]]

-- | This is a shortcut to build a query plan and execute in one step,
-- with no bindings provided.  It doesn't make sense to have bindings
-- in one-shot queries.
queryDatabase :: (Failure DatalogError m, Eq a, Hashable a, Show a)
                 => Database a -- ^ The intensional database of facts
                 -> QueryBuilder m a (Query a) -- ^ A monad building up a set of rules and returning a Query
                 -> m [[a]]
queryDatabase idb qm = do
  qp <- buildQueryPlan idb qm
  executeQueryPlan qp idb []

-- | Given a query description, build a query plan by stratifying the
-- rules and performing the magic sets transformation.  Throws an
-- error if the rules cannot be stratified.
buildQueryPlan :: (Failure DatalogError m, Eq a, Hashable a, Show a)
                  => Database a
                  -> QueryBuilder m a (Query a)
                  -> m (QueryPlan a)
buildQueryPlan idb qm = do
  let ipreds = databaseRelations idb
  (q, rs) <- runQuery qm idb
  rs' <- magicSetsRules ipreds q rs
  strata <- stratifyRules rs'
  return $! QueryPlan q strata

-- | Execute a query plan with an intensional database and a set of
-- bindings (substituted in for 'BindVar's).  Throw an error if:
--
--  * The rules and database define the same relation
executeQueryPlan :: (Failure DatalogError m, Eq a, Hashable a, Show a)
                    => QueryPlan a -> Database a -> [(Text, a)] -> m [[a]]
executeQueryPlan (QueryPlan q strata) idb bindings = do
  -- FIXME: Bindings is used to substitute in values for BoundVars in
  -- the query.  Those might actually affect the magic rules that are
  -- required...  This is the seed-rule and
  -- seed-predicate-for-insertion code in the clojure implementation
  edb <- applyStrata strata idb
  let q' = bindQuery q bindings
      pt = queryToPartialTuple q'
      p = queryPredicate q'
  return $! map unTuple $ select edb p pt

-- Private helpers

-- | Apply the rules in each stratum bottom-up.  Compute a fixed-point
-- for each stratum
applyStrata :: (Failure DatalogError m, Eq a, Hashable a, Show a)
               => [[Rule a]] -> Database a -> m (Database a)
applyStrata [] db = return db
applyStrata ss@(s:strata) db = do
  -- Group the rules by their head relations.  The delta table has to
  -- be managed for all of the related rules at once.
  db' <- foldM applyRuleSet db (partitionRules s)
  case databaseHasDelta db' of
    True -> applyStrata ss db'
    False -> applyStrata strata db'
