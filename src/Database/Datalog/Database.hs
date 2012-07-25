{-# LANGUAGE DeriveDataTypeable, FlexibleContexts #-}
module Database.Datalog.Database (
  Relation(..),
  Database,
  DatabaseBuilder,
  Tuple(..),
  -- * Functions
  makeDatabase,
  addRelation,
  assertFact,
  databaseRelations,
  databaseRelation,
  dataForRelation,
  addTupleToRelation,
  replaceRelation,
  ensureDatabaseRelation,
  resetRelationDelta,
  withDeltaRelation,
  databaseHasDelta
  ) where

import Control.Failure
import Control.Monad.State.Strict
import Data.Hashable
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import Data.HashSet ( HashSet )
import qualified Data.HashSet as HS
import Data.Monoid
import Data.Text ( Text )

import Database.Datalog.Errors

import Debug.Trace
debug = flip trace

-- | A wrapper around lists that lets us more easily hide length
-- checks
newtype Tuple a = Tuple { unTuple ::  [a] }
                deriving (Eq, Show)

instance (Hashable a) => Hashable (Tuple a) where
  hash (Tuple es) = hash es

-- | A relation whose elements are fixed-length lists of a
-- user-defined type.  This is only used internally and is not exposed
-- to the user.
data DBRelation a = DBRelation { relationArity :: !Int
                               , relationName :: !Text
                               , relationData :: [Tuple a]
                               , relationMembers :: !(HashSet (Tuple a))
                               , relationDelta :: [Tuple a]
                               , relationIndex :: !(HashMap (Int, a) (Tuple a))
                               }
                  deriving (Show)

instance (Eq a, Hashable a) => Eq (DBRelation a) where
  (DBRelation arity1 n1 _ ms1 _ _) == (DBRelation arity2 n2 _ ms2 _ _) =
    arity1 == arity2 && n1 == n2 && ms1 == ms2

-- | A database is a collection of facts organized into relations
newtype Database a = Database (HashMap Text (DBRelation a))

instance (Show a) => Show (Database a) where
  show (Database db) = show db

instance (Eq a, Hashable a) => Eq (Database a) where
  (Database db1) == (Database db2) = db1 == db2

-- | A wrapper to expose the relation name to callers without
-- revealing details of its implementation
newtype Relation = Relation Text
                 deriving (Eq, Ord, Show)

instance Hashable Relation where
  hash (Relation t) = hash t

-- | The monad in which databases are constructed and initial facts
-- are asserted
type DatabaseBuilder m a = StateT (Database a) m

-- | Make a new fact Database in a DatabaseBuilder monad.  It can
-- fail, and errors will be returned however the caller indicates.
makeDatabase :: (Failure DatalogError m)
                => DatabaseBuilder m a () -> m (Database a)
makeDatabase b = execStateT b (Database mempty)

-- | Add a relation to the 'Database'.  If the relation exists, an
-- error will be raised.  The function returns a 'RelationHandle' that
-- can be used in conjuction with 'addTuple'.
addRelation :: (Failure DatalogError m, Eq a, Hashable a)
               => Text -> Int -> DatabaseBuilder m a Relation
addRelation name arity = do
  Database m <- get
  case HM.lookup name m of
    Just _ -> lift $ failure (RelationExistsError name)
    Nothing -> do
      let r = DBRelation arity name mempty mempty mempty mempty
      put $! Database $! HM.insert name r m
      return $! Relation name

-- | Add a tuple to the named 'Relation' in the database.  If the
-- tuple is already present, the original 'Database' is unchanged.
assertFact :: (Failure DatalogError m, Eq a, Hashable a)
            => Relation -> [a] -> DatabaseBuilder m a ()
assertFact relHandle@(Relation t) tup = do
  db@(Database m) <- get
  let rel = databaseRelation db relHandle
  wrappedTuple <- toWrappedTuple rel tup
  case HS.member wrappedTuple (relationMembers rel) of
    True -> return ()
    False ->
      let rel' = addTupleToRelation' rel wrappedTuple
      in put $! Database $ HM.insert t rel' m

-- | Replace a relation in the database.  The old relation is
-- discarded completely, so be sure to initialize the replacement with
-- all of the currently known facts.
replaceRelation :: Database a -> DBRelation a -> Database a
replaceRelation (Database db) r =
  Database $ HM.insert (relationName r) r db

-- | Add a tuple to the relation without updating the delta table.
-- This is needed for the initial database construction.
addTupleToRelation' :: (Eq a, Hashable a) => DBRelation a -> Tuple a -> DBRelation a
addTupleToRelation' rel t =
  case HS.member t (relationMembers rel) of
    True -> rel
    False -> rel { relationData = t : relationData rel
                 , relationMembers = HS.insert t (relationMembers rel)
                 }

-- | Add the given tuple to the given 'Relation'.  It updates the
-- index in the process.  The 'Tuple' is already validated so this is
-- a total function.
--
-- It has already been verified that the tuple does not exist in the
-- relation (see 'addTuple') so no extra checks are required here.
addTupleToRelation :: (Eq a, Hashable a, Show a) => DBRelation a -> Tuple a -> DBRelation a
addTupleToRelation rel t =
  case HS.member t (relationMembers rel) of
    True -> rel
    False -> rel { relationData = t : relationData rel
                 , relationMembers = HS.insert t (relationMembers rel)
                 , relationDelta = t : relationDelta rel
                 }

-- | If the requested relation is not in the database, just use the
-- original database (the result is the same - an empty relation)
withDeltaRelation :: Database a -> Relation -> (Database a -> b) -> b
withDeltaRelation d@(Database db) (Relation r) action =
  action $ case HM.lookup r db of
    Nothing -> d
    Just dbrel ->
      let rel' = dbrel { relationData = relationDelta dbrel }
      in Database $ HM.insert r rel' db

resetRelationDelta :: DBRelation a -> DBRelation a
resetRelationDelta rel = rel { relationDelta = mempty }

-- | Get a relation by name.  If it does not exist in the database,
-- return a new relation with the appropriate arity.
ensureDatabaseRelation :: (Eq a, Hashable a)
                          => Database a -> Relation -> Int -> DBRelation a
ensureDatabaseRelation (Database m) (Relation t) arity =
  case HM.lookup t m of
    Just r -> r
    Nothing -> DBRelation arity t mempty mempty mempty mempty

-- | Get an existing relation from the database
databaseRelation :: Database a -> Relation -> DBRelation a
databaseRelation (Database m) (Relation t) =
  case HM.lookup t m of
    -- This really shouldn't be possible - it would be an error in the
    -- API since users can't create them and they can only be obtained
    -- in the same monad with the Database
    Nothing -> error ("Invalid RelationHandle: " ++ show t)
    Just r -> r

-- | Get all of the predicates referenced in the database
databaseRelations :: Database a -> [Relation]
databaseRelations (Database m) =
  map Relation (HM.keys m)

-- | Get all of the tuples for the given predicate/relation in the database.
dataForRelation :: (Failure DatalogError m)
                        => Database a -> Relation -> m [Tuple a]
dataForRelation (Database m) (Relation txt) =
  case HM.lookup txt m of
    Nothing -> failure $ NoRelationError txt
    Just r -> return $ relationData r

databaseHasDelta :: Database a -> Bool
databaseHasDelta (Database db) =
  any (not . null . relationDelta) (HM.elems db) `debug` show (map toDbg (HM.elems db))
  where
    toDbg r = show (relationName r) ++ ": " ++ show (not (null (relationDelta r)))

-- | Convert the user-level tuple to a safe length-checked Tuple.
-- Signals failure (according to @m@) if the length is invalid.
--
-- FIXME: It would also be nice to be able to check the column type...
toWrappedTuple :: (Failure DatalogError m)
                  => DBRelation a -> [a] -> DatabaseBuilder m a (Tuple a)
toWrappedTuple rel tup =
  case relationArity rel == length tup of
    False -> lift $ failure (SchemaError (relationName rel))
    True -> return $! Tuple tup
