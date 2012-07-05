{-# LANGUAGE FlexibleContexts #-}
module Database.Datalog (
  -- * Types
  Database,
  QueryPlan,

  -- * Evaluating Queries
  queryDatabase,
  buildQueryPlan,
  executeQueryPlan
  ) where

import Control.Failure
import Control.Monad.State.Strict ( runStateT )
import Data.Text ( Text )

import Database.Datalog.Database
import Database.Datalog.Errors
import Database.Datalog.Rules
import Database.Datalog.MagicSets
import Database.Datalog.Stratification

-- | A fully-stratified query plan
data QueryPlan a = QueryPlan [[Rule a]]

-- | This is a shortcut ot build a query plan and execute in one step,
-- with no bindings provided.  It doesn't make sense to have bindings
-- in one-shot queries.
queryDatabase :: (Failure DatalogError m)
                 => Database a -- ^ The intensional database of facts
                 -> QueryMonad m a (Query a) -- ^ A monad building up a set of rules and returning a Query
                 -> m [Tuple a]
queryDatabase idb qm = do
  qp <- buildQueryPlan idb qm
  executeQueryPlan qp idb []

-- | Given a query description, build a query plan by stratifying the
-- rules and performing the magic sets transformation.  Throws an
-- error if the rules cannot be stratified.
buildQueryPlan :: (Failure DatalogError m)
                  => Database a
                  -> QueryMonad m a (Query a)
                  -> m (QueryPlan a)
buildQueryPlan idb qm = do
  let ipreds = databasePredicates idb
  (q, QueryState _ rs) <- runStateT qm (QueryState idb [])
  rs' <- magicSetsRules ipreds q rs
  strata <- stratifyRules rs'
  return $! QueryPlan strata


-- | Execute a query plan with an intensional database and a set of
-- bindings (substituted in for 'BindVar's).  Throw an error if:
--
--  * The rules and database define the same relation
executeQueryPlan :: (Failure DatalogError m)
                    => QueryPlan a -> Database a -> [(Text, a)] -> m [Tuple a]
executeQueryPlan qp idb bindings = undefined
