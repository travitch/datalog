module Database.Datalog.Relation (
  Relation(..)
  ) where

import Data.Hashable
import Data.Text ( Text, unpack )
import Text.Printf

import Database.Datalog.Adornment

-- Let Relation be user exposed, use this for internal versions:
--
-- data InternalRelation = InternalRelation BindingPattern Text
--                       | MagicRelation BindingPattern Text


-- | A wrapper to expose the relation name to callers without
-- revealing details of its implementation
data Relation = Relation Text
              | MagicRelation BindingPattern Text
              deriving (Eq, Ord)

instance Show Relation where
  show (Relation t) = unpack t
  show (MagicRelation bs t) = printf "Magic_%s[%s]" (unpack t) (show bs)

-- FIXME: May need a new relation that tracks its binding pattern,
-- too.  This is probably important for cases where the same relation
-- appears in the same body literal with different binding patterns in
-- a given rule.  These seem like they should be referencing different
-- tables...
--
-- The transformRules step will have to be the one to do the
-- translation

instance Hashable Relation where
  hashWithSalt s (Relation t) =
    s `hashWithSalt` t `hashWithSalt` (99 :: Int)
  hashWithSalt s (MagicRelation p t) =
    s `hashWithSalt` p `hashWithSalt` (2 :: Int)
