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
import Control.Monad ( foldM )
import Data.Hashable
import Data.Text ( Text )

import Database.Datalog.Database
import Database.Datalog.Errors
import Database.Datalog.Rules
import Database.Datalog.MagicSets
import Database.Datalog.Stratification

-- | A fully-stratified query plan
data QueryPlan a = QueryPlan (Query a) [[Rule a]]

-- | This is a shortcut to build a query plan and execute in one step,
-- with no bindings provided.  It doesn't make sense to have bindings
-- in one-shot queries.
queryDatabase :: (Failure DatalogError m, Eq a, Hashable a)
                 => Database a -- ^ The intensional database of facts
                 -> QueryMonad m a (Query a) -- ^ A monad building up a set of rules and returning a Query
                 -> m [Tuple a]
queryDatabase idb qm = do
  qp <- buildQueryPlan idb qm
  executeQueryPlan qp idb []

-- | Given a query description, build a query plan by stratifying the
-- rules and performing the magic sets transformation.  Throws an
-- error if the rules cannot be stratified.
buildQueryPlan :: (Failure DatalogError m, Eq a, Hashable a)
                  => Database a
                  -> QueryMonad m a (Query a)
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
                    => QueryPlan a -> Database a -> [(Text, a)] -> m [Tuple a]
executeQueryPlan (QueryPlan q strata) idb bindings = do
  idb' <- executePlan' strata idb
  select q idb'

-- | Execute the query plan until no new facts are added to the database
executePlan' :: (Failure DatalogError m, Eq a, Hashable a)
                => [[Rule a]] -> Database a -> m (Database a)
executePlan' strata db = do
  db' <- applyStrata strata db
  case databasesDiffer db db' of
    True -> executePlan' strata db'
    False -> return db'

-- | Select the facts relevant to the query from the database
select :: (Failure DatalogError m) => Query a -> Database a -> m [Tuple a]
select = undefined

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
