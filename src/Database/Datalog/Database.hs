{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeInType #-}
module Database.Datalog.Database (
  Relation,
  Database,
  DatabaseBuilder,
  -- * Functions
  makeDatabase,
  lookupRelation,
  addRelation,
  assertFact,
  databaseRelations,
  databaseRelation,
  dataForRelation,
  addTupleToRelation,
  addTupleToRelation',
  replaceRelation,
  ensureDatabaseRelation,
  resetRelationDelta,
  withDeltaRelation,
  databaseHasDelta
  ) where

import qualified Control.Monad.Catch as E
import qualified Control.Monad.State.Strict as CMS
import qualified Data.Foldable as F
import           Data.Functor.Const ( Const(..) )
import qualified Data.HashSet as HS
import           Data.Kind ( Type )
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some ( Some(..), viewSome )
import qualified Data.Text as T
import           Data.Typeable ( Typeable )

import           Prelude

import qualified Database.Datalog.Errors as DDE
import qualified Database.Datalog.RelationSchema as DDR
import qualified Database.Datalog.Tuple as DDT
import qualified Database.Datalog.Panic as DDP

-- | A relation whose elements are fixed-length lists of a
-- user-defined type.  This is only used internally and is not exposed
-- to the user.
data Relation a r tps =
  Relation { relationSchema :: !(DDR.RelationSchema r tps)
           , relationData :: HS.HashSet (DDT.Tuple a tps)
           , relationDelta :: HS.HashSet (DDT.Tuple a tps)
           }

-- | A database is a collection of facts organized into relations
data Database (a :: k -> Type) (r :: k -> Type) =
  Database { relations :: MapF.MapF (DDR.RelationSchema r) (Relation a r)
           -- ^ The relation store containing (unboxed) tuples
           , atomStore :: MapF.MapF r (AtomStore a)
           , ids :: Int
           }

-- | A mapping between unique identifiers and atoms
--
-- Atoms are the ground values referenced in the initial set of facts provided
-- to the system.  We reduce them to 'Int' in internal tuples to make the core
-- as efficient as possible.
data AtomStore a tp =
  AtomStore { toAtom :: Map.Map Int (a tp)
            , fromAtom :: MapF.MapF a (Const Int)
            }

-- | The monad in which databases are constructed and initial facts
-- are asserted
newtype DatabaseBuilder m a r v =
  DatabaseBuilder { unDBB :: CMS.StateT (Database a r) m v }
  deriving ( Functor
           , Applicative
           , Monad
           , CMS.MonadState (Database a r)
           , E.MonadThrow
           )

lookupRelation :: (PC.OrdF r) => DDR.RelationSchema r tps -> Database a r -> Maybe (Relation a r tps)
lookupRelation schema db = MapF.lookup schema (relations db)

emptyDatabase :: Database a r
emptyDatabase = Database { relations = MapF.empty
                         , atomStore = MapF.empty
                         , ids = 0
                         }

-- | Make a new fact Database in a DatabaseBuilder monad.  It can
-- fail, and errors will be returned however the caller indicates.
makeDatabase :: (E.MonadThrow m)
             => DatabaseBuilder m a r ()
             -> m (Database a r)
makeDatabase b = CMS.execStateT (unDBB b) emptyDatabase

-- | Add a relation to the 'Database'.  If the relation exists, an
-- error will be raised.  The function returns a 'DDR.RelationSchema' that
-- can be used in conjuction with 'addTuple'.
addRelation :: forall m k (a :: k -> Type) (r :: k -> Type) tps
             . (E.MonadThrow m, Typeable k, Typeable r, PC.OrdF r)
            => T.Text
            -> Ctx.Assignment r tps
            -> DatabaseBuilder m a r (DDR.RelationSchema r tps)
addRelation name reprs = do
  rm <- CMS.gets relations
  let relNames = fmap (viewSome DDR.relationSchemaName) (MapF.keys rm)
  case name `elem` relNames of
    True -> E.throwM (DDE.RelationExistsError @k @r name)
    False -> do
      let r = Relation { relationSchema = rel
                       , relationData = HS.empty
                       , relationDelta = HS.empty
                       }
      CMS.modify' $ \db -> db { relations = MapF.insert rel r (relations db) }
      return rel
  where
    rel = DDR.RelationSchema reprs name

-- | Add a tuple to the named 'Relation' in the database.  If the
-- tuple is already present, the original 'Database' is unchanged.
assertFact :: (E.MonadThrow m, PC.OrdF r, PC.OrdF a)
           => DDR.RelationSchema r tps
           -> Ctx.Assignment a tps
           -> DatabaseBuilder m a r ()
assertFact schema values = do
  db0 <- CMS.get
  let rel = databaseRelation db0 schema
  tuple <- mkTuple schema values
  case HS.member tuple (relationData rel) of
    True -> return ()
    False -> do
      let rel' = addTupleToRelation' rel tuple
      CMS.modify' $ \db -> db { relations = MapF.insert schema rel' (relations db) }

mkTuple :: (PC.OrdF a, PC.OrdF r, Monad m)
        => DDR.RelationSchema r tps
        -> Ctx.Assignment a tps
        -> DatabaseBuilder m a r (DDT.Tuple a tps)
mkTuple schema vals = do
  let reprs = DDR.relationSchemaReprs schema
  DDT.generateM reprs $ \idx -> do
    let repr = reprs Ctx.! idx
    let val = vals Ctx.! idx
    atomIdentifier repr val

atomIdentifier :: (PC.OrdF a, PC.OrdF r, Monad m) => r tp -> a tp -> DatabaseBuilder m a r Int
atomIdentifier repr atom = do
  store0 <- CMS.gets atomStore
  case MapF.lookup repr store0 of
    Just as0 ->
      case MapF.lookup atom (fromAtom as0) of
        Just (Const i) -> return i
        Nothing -> do
          nextId <- CMS.gets ids
          let as1 = as0 { fromAtom = MapF.insert atom (Const nextId) (fromAtom as0)
                        , toAtom = Map.insert nextId atom (toAtom as0)
                        }
          CMS.modify' $ \db -> db { ids = nextId + 1
                                  , atomStore = MapF.insert repr as1 (atomStore db)
                                  }
          return nextId
    Nothing -> do
      nextId <- CMS.gets ids
      let as0 = AtomStore { fromAtom = MapF.singleton atom (Const nextId)
                          , toAtom = Map.singleton nextId atom
                          }
      CMS.modify' $ \db -> db { ids = nextId + 1
                              , atomStore = MapF.insert repr as0 (atomStore db)
                              }
      return nextId

-- | Replace a relation in the database.  The old relation is
-- discarded completely, so be sure to initialize the replacement with
-- all of the currently known facts.
replaceRelation :: (PC.OrdF r) => Database a r -> Relation a r tps -> Database a r
replaceRelation db r =
  db { relations = MapF.insert (relationSchema r) r (relations db) }

-- | Add a tuple to the relation without updating the delta table.
-- This is needed for the initial database construction.
addTupleToRelation' :: Relation a r tps -> DDT.Tuple a tps -> Relation a r tps
addTupleToRelation' rel t =
  rel { relationData = HS.insert t (relationData rel) }

-- | Add the given tuple to the given 'Relation'.  It updates the
-- index in the process.  The 'Tuple' is already validated so this is
-- a total function.
--
-- It has already been verified that the tuple does not exist in the
-- relation (see 'addTuple') so no extra checks are required here.
addTupleToRelation :: Relation a r tps -> DDT.Tuple a tps -> Relation a r tps
addTupleToRelation rel t =
  case HS.member t (relationData rel)  || HS.member t (relationDelta rel) of
    True -> rel
    False -> rel { relationData = HS.insert t (relationData rel)
                 , relationDelta = HS.insert t (relationDelta rel)
                 }

-- | If the requested relation is not in the database, just use the
-- original database (the result is the same - an empty relation)
withDeltaRelation :: (PC.OrdF r) => Database a r -> DDR.RelationSchema r tps -> (Database a r -> b) -> b
withDeltaRelation db r action =
  action $ case MapF.lookup r (relations db) of
    Nothing -> db
    Just dbrel ->
      let rel' = dbrel { relationData = relationDelta dbrel }
      in db { relations = MapF.insert r rel' (relations db) }

resetRelationDelta :: Relation a r tps -> Relation a r tps
resetRelationDelta rel = rel { relationDelta = mempty }

-- | Get a relation by name.  If it does not exist in the database,
-- return a new relation with the appropriate arity.
ensureDatabaseRelation :: (PC.OrdF r) => Database a r -> DDR.RelationSchema r tps -> Relation a r tps
ensureDatabaseRelation db rel =
  case MapF.lookup rel (relations db) of
    Just r -> r
    Nothing -> Relation { relationSchema = rel
                        , relationData = HS.empty
                        , relationDelta = HS.empty
                        }

-- | Get an existing relation from the database
databaseRelation :: (PC.OrdF r) => Database a r -> DDR.RelationSchema r tps -> Relation a r tps
databaseRelation db rel =
  case MapF.lookup rel (relations db) of
    -- This really shouldn't be possible - it would be an error in the
    -- API since users can't create them and they can only be obtained
    -- in the same monad with the Database
    Nothing -> DDP.panic DDP.DatalogCore "databaseRelation" ["Invalid RelationSchema: " ++ show rel]
    Just r -> r

-- | Get all of the predicates referenced in the database
databaseRelations :: Database a r -> [Some (DDR.RelationSchema r)]
databaseRelations db = MapF.keys (relations db)

-- | Get all of the tuples for the given predicate/relation in the database.
dataForRelation :: forall m k (a :: k -> Type) (r :: k -> Type) tps
                 . (E.MonadThrow m, PC.OrdF r, Typeable k, Typeable r)
                => Database a r
                -> DDR.RelationSchema r tps
                -> m [DDT.Tuple a tps]
dataForRelation db rel =
  case MapF.lookup rel (relations db) of
    Nothing -> E.throwM $ DDE.NoRelationError @k @r rel
    Just r -> return (F.toList (relationData r))

databaseHasDelta :: Database a r -> Bool
databaseHasDelta db =
  any relationHasDelta (MapF.elems (relations db)) --  `debug` show (map toDbg (HM.elems db))
  where
    relationHasDelta (Some rel) =
      not (HS.null (relationDelta rel))
  -- where
  --   toDbg r = show (relationName r) ++ ": " ++ show (not (null (relationDelta r)))

