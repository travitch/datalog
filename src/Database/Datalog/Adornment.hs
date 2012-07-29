module Database.Datalog.Adornment (
  Binding(..),
  BindingPattern(..),
  Adornment(..)
  ) where

import Data.Hashable

data Binding = B {- Bound -} | F {- Free -}
             deriving (Eq, Ord, Show)

instance Hashable Binding where
  hash B = 105
  hash F = 709

newtype BindingPattern = BindingPattern { bindingPattern :: [Binding] }
                       deriving (Eq, Ord)

instance Show BindingPattern where
  show (BindingPattern bs) = concatMap show bs

instance Hashable BindingPattern where
  hash (BindingPattern bs) = hash bs

data Adornment = Free !Int -- ^ The index to bind a free variable
               | BoundAtom
               | Bound !Int -- ^ The index to look for the binding of this variable
               deriving (Eq, Show)

instance Hashable Adornment where
  hash (Free i) = 1 `combine` hash i
  hash BoundAtom = 7776
  hash (Bound i) = 2 `combine` hash i
