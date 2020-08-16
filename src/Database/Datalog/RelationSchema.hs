{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
module Database.Datalog.RelationSchema (
  RelationSchema(..),
  relationSchemaName,
  relationSchemaReprs
  ) where

import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TH.GADT as PTH
import qualified Data.Text as T
import           Text.Printf ( printf )

import           Database.Datalog.Adornment

-- | A wrapper to expose the relation name to callers without
-- revealing details of its implementation
data RelationSchema r tps where
  RelationSchema :: Ctx.Assignment r tps -> T.Text -> RelationSchema r tps
  MagicRelationSchema :: Ctx.Assignment r tps -> T.Text -> BindingPattern -> RelationSchema r tps

relationSchemaName :: RelationSchema r tps -> T.Text
relationSchemaName rs =
  case rs of
    RelationSchema _reprs name -> name
    MagicRelationSchema _reprs name _pattern -> name

relationSchemaReprs :: RelationSchema r tps -> Ctx.Assignment r tps
relationSchemaReprs rs =
  case rs of
    RelationSchema reprs _ -> reprs
    MagicRelationSchema reprs _name _pattern -> reprs

instance PC.ShowF (RelationSchema r) where
  showF (RelationSchema _ t) = T.unpack t
  showF (MagicRelationSchema _ t bs) = printf "Magic_%s[%s]" (T.unpack t) (show bs)

instance Show (RelationSchema r tps) where
  show (RelationSchema _ t) = T.unpack t
  show (MagicRelationSchema _ t bs) = printf "Magic_%s[%s]" (T.unpack t) (show bs)

$(return [])

instance (PC.TestEquality r) => PC.TestEquality (RelationSchema r) where
  testEquality = $(PTH.structuralTypeEquality [t|RelationSchema|]
                   [ (PTH.ConType [t|Ctx.Assignment|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType, [|PC.testEquality|]) ]
                  )

instance (PC.OrdF r) => PC.OrdF (RelationSchema r) where
  compareF = $(PTH.structuralTypeOrd [t|RelationSchema|]
              [(PTH.ConType [t|Ctx.Assignment|] `PTH.TypeApp` PTH.AnyType `PTH.TypeApp` PTH.AnyType, [|PC.compareF|]) ]
              )


-- FIXME: May need a new relation that tracks its binding pattern,
-- too.  This is probably important for cases where the same relation
-- appears in the same body literal with different binding patterns in
-- a given rule.  These seem like they should be referencing different
-- tables...
--
-- The transformRules step will have to be the one to do the
-- translation

-- instance Hashable Relation where
--   hashWithSalt s (Relation t) =
--     s `hashWithSalt` t `hashWithSalt` (99 :: Int)
--   hashWithSalt s (MagicRelation p t) =
--     s `hashWithSalt` p `hashWithSalt` t `hashWithSalt` (2 :: Int)
