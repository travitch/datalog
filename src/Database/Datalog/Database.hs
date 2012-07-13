{-# LANGUAGE DeriveDataTypeable, FlexibleContexts #-}
module Database.Datalog.Database (
  Schema,
  Relation(..),
  Database,
  DatabaseBuilder,
  Predicate(..),
  Tuple(..),
  -- * Functions
  makeDatabase,
  addRelation,
  assertFact,
  databasePredicates,
  databasesDiffer
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

-- | The schema of a relation, naming each column
newtype Schema = Schema [Text]
               deriving (Show)

-- | A wrapper around lists that lets us more easily hide length
-- checks
newtype Tuple a = Tuple [a]
                deriving (Eq, Show)

instance (Hashable a) => Hashable (Tuple a) where
  hash (Tuple es) = hash es



data Predicate = RelationPredicate Relation
               | InferencePredicate Text
               deriving (Eq)

instance Hashable Predicate where
  hash (InferencePredicate t) = hash t
  hash (RelationPredicate (Relation t)) = hash t

-- | A relation whose elements are fixed-length lists of a
-- user-defined type.  This is only used internally and is not exposed
-- to the user.
data DBRelation a = DBRelation { relationSchema :: Schema
                               , relationName :: Text
                               , relationData :: HashSet (Tuple a)
                               , relationIndex :: HashMap (Int, a) (Tuple a)
                               }
                  deriving (Show)

data Database a = Database (HashMap Text (DBRelation a))

instance Monoid (Database a) where
  mempty = Database mempty
  mappend (Database m1) (Database m2) =
    Database (HM.unionWith mergeRelations m1 m2)

newtype Relation = Relation Text
                 deriving (Eq)
type DatabaseBuilder m a = StateT (Database a) m

databasesDiffer :: Database a -> Database a -> Bool
databasesDiffer (Database db1) (Database db2) =
  counts db1 /= counts db2
  where
    counts = fmap countData
    countData (DBRelation _ _ s _) = HS.size s

-- | Make a new fact Database in a DatabaseBuilder monad.  It can
-- fail, and errors will be returned however the caller indicates.
makeDatabase :: (Failure DatalogError m)
                => DatabaseBuilder m a () -> m (Database a)
makeDatabase b = execStateT b mempty

-- | Add a tuple to the named 'Relation' in the database.  If the
-- tuple is already present, the original 'Database' is unchanged.
assertFact :: (Failure DatalogError m, Eq a, Hashable a)
            => Relation -> [a] -> DatabaseBuilder m a ()
assertFact relHandle@(Relation t) tup = do
  db@(Database m) <- get
  let rel = databaseRelation db relHandle
  wrappedTuple <- toWrappedTuple rel tup
  case HS.member wrappedTuple (relationData rel) of
    True -> return ()
    False ->
      let rel' = addTupleToRelation rel wrappedTuple
      in put $! Database $ HM.insert t rel' m

-- | Add a relation to the 'Database'.  If the relation exists, an
-- error will be raised.  The function returns a 'RelationHandle' that
-- can be used in conjuction with 'addTuple'.
addRelation :: (Failure DatalogError m, Eq a, Hashable a)
               => Text -> Schema -> DatabaseBuilder m a Relation
addRelation name schema = do
  Database m <- get
  case HM.lookup name m of
    Just _ -> lift $ failure (RelationExistsError name)
    Nothing -> do
      let r = DBRelation schema name mempty mempty
      put $! Database $! HM.insert name r m
      return $! Relation name

-- | Convert the user-level tuple to a safe length-checked Tuple.
-- Signals failure (according to @m@) if the length is invalid.
--
-- FIXME: It would also be nice to be able to check the column type...
toWrappedTuple :: (Failure DatalogError m)
                  => DBRelation a -> [a] -> DatabaseBuilder m a (Tuple a)
toWrappedTuple rel tup =
  case length s == length tup of
    False -> lift $ failure (SchemaError (relationName rel))
    True -> return $! Tuple tup
  where
    Schema s = relationSchema rel

-- | Add the given tuple to the given 'Relation'.  It updates the
-- index in the process.  The 'Tuple' is already validated so this is
-- a total function.
--
-- It has already been verified that the tuple does not exist in the
-- relation (see 'addTuple') so no extra checks are required here.
addTupleToRelation :: (Eq a, Hashable a) => DBRelation a -> Tuple a -> DBRelation a
addTupleToRelation rel t@(Tuple elems) =
  rel { relationData = HS.insert t (relationData rel)
      , relationIndex = foldr updateIndex (relationIndex rel) (zip [0..] elems)
      }
  where
    updateIndex ie = HM.insert ie t

databaseRelation :: Database a -> Relation -> DBRelation a
databaseRelation (Database m) (Relation t) =
  case HM.lookup t m of
    -- This really shouldn't be possible - it would be an error in the
    -- API since users can't create them and they can only be obtained
    -- in the same monad with the Database
    Nothing -> error ("Invalid RelationHandle: " ++ show t)
    Just r -> r

mergeRelations :: DBRelation a -> DBRelation a -> DBRelation a
mergeRelations = undefined

databasePredicates :: Database a -> [Predicate]
databasePredicates (Database m) =
  map (RelationPredicate . Relation) (HM.keys m)
