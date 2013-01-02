module Database.Datalog.Adornment (
  Binding(..),
  BindingPattern(..),
  Adornment(..)
  ) where

import Data.Hashable

data Binding = B {- Bound -} | F {- Free -}
             deriving (Eq, Ord, Show)

instance Hashable Binding where
  hashWithSalt s B = s `hashWithSalt` (105 :: Int)
  hashWithSalt s F = s `hashWithSalt` (709 :: Int)

newtype BindingPattern = BindingPattern { bindingPattern :: [Binding] }
                       deriving (Eq, Ord)

instance Show BindingPattern where
  show (BindingPattern bs) = concatMap show bs

instance Hashable BindingPattern where
  hashWithSalt s (BindingPattern bs) = s `hashWithSalt` bs

data Adornment = Free !Int -- ^ The index to bind a free variable
               | BoundAtom
               | Bound !Int -- ^ The index to look for the binding of this variable
               deriving (Eq, Show)

instance Hashable Adornment where
  hashWithSalt s BoundAtom = s `hashWithSalt` (7776 :: Int)
  hashWithSalt s (Free i) =
    s `hashWithSalt` (1 :: Int) `hashWithSalt` i
  hashWithSalt s (Bound i) =
    s `hashWithSalt` (2 :: Int) `hashWithSalt` i
