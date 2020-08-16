{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeInType #-}
-- | An abstraction over database tuples
--
-- Tuples carry only 'Int's for efficient comparison; the outer layers of the
-- library orchestrate mapping domain values to those 'Int's.
--
-- This module leaves the Tuple type totally abstract so that the internal
-- representation is open to experimentation.
module Database.Datalog.Tuple (
  Tuple,
  generate,
  generateM,
  index
  ) where

import           Control.Monad.ST ( ST )
import qualified Data.Hashable as H
import           Data.Kind ( Type )
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Vector.Primitive as VP
import qualified Data.Vector.Primitive.Mutable as VPM
import qualified Data.Primitive.ByteArray as DP

-- | A database tuple
--
-- The type parameters are phantom to support provably-safe indexing
newtype Tuple (a :: k -> Type) tps = Tuple (VP.Vector Int)
  deriving (Eq, Ord, Show)

instance H.Hashable (Tuple a tps) where
  hashWithSalt slt (Tuple (VP.Vector off len (DP.ByteArray bytes))) =
    let bhash = H.hashByteArray bytes off len
    in slt `H.hashWithSalt` off
        `H.hashWithSalt` len
        `H.hashWithSalt` bhash

generate :: forall a r tps
          . Ctx.Assignment r tps
         -> (forall tp . Ctx.Index tps tp -> Int)
         -> Tuple a tps
generate reprs g = Tuple $! VP.create initEntries
  where
    initEntries :: forall s . ST s (VPM.MVector s Int)
    initEntries = do
      let sz = Ctx.size reprs
      v <- VPM.new (Ctx.sizeInt sz)
      let initializeEntry :: forall tp . ST s () -> Ctx.Index tps tp -> ST s ()
          initializeEntry _ idx = do
            VPM.write v (Ctx.indexVal idx) (g idx)
      Ctx.forIndex sz initializeEntry (return ())
      return v

generateM :: (Monad m)
          => Ctx.Assignment r tps
          -> (forall tp . Ctx.Index tps tp -> m Int)
          -> m (Tuple a tps)
generateM reprs g = do
  let sz = Ctx.size reprs
  action <- Ctx.forIndex sz (vectorWriteGenerator g) (return (Gen (\_ -> return ())))
  let v = VP.create (doCreate (Ctx.sizeInt sz) action)
  return (Tuple v)
  where
    doCreate :: Int -> Gen -> forall s . ST s (VPM.MVector s Int)
    doCreate isz (Gen action) = do
      vec0 <- VPM.new isz
      action vec0
      return vec0

data Gen = Gen (forall s . VPM.MVector s Int -> ST s ())

vectorWriteGenerator :: (Monad m)
                     => (forall tp . Ctx.Index tps tp -> m Int)
                     -> m Gen
                     -> Ctx.Index tps tp0
                     -> m Gen
vectorWriteGenerator g acc idx = do
  ival <- g idx
  Gen mkVec <- acc
  let action :: forall s . VPM.MVector s Int -> ST s ()
      action vec = do
        -- Chain the previous initialization actions through this one
        mkVec vec
        VPM.write vec (Ctx.indexVal idx) ival
  return (Gen action)

index :: Tuple a tps -> Ctx.Index tps tp -> Int
index (Tuple v) idx = v VP.! Ctx.indexVal idx

{- Note [Tuple Representations]

There are a number of possible representations here.

1. Unboxed tuples

   These admit very efficient comparison and are compact in memory

2. Sequences

   Takes more memory, but admits significant sharing of prefixes

-}
