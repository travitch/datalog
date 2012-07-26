module Database.Datalog.Relation (
  Relation(..)
  ) where

import Data.Hashable
import Data.Text ( Text )

-- | A wrapper to expose the relation name to callers without
-- revealing details of its implementation
newtype Relation = Relation Text
                 deriving (Eq, Ord, Show)

instance Hashable Relation where
  hash (Relation t) = hash t
