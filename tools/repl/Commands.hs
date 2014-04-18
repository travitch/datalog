module Commands (
  Command(..),
  LiteralValue(..),
  AnyValue(..),
  Clause(..)
  ) where

data LiteralValue = LVString String
                  deriving (Eq, Ord, Show)

data AnyValue = AVLiteral LiteralValue
              | AVVariable String
              deriving (Eq, Ord, Show)

-- | The list is a string of variable names
data Clause v = Clause String [v]
            deriving (Eq, Ord, Show)

data Command = Quit
             | AssertFact (Clause LiteralValue)
             | Query (Clause AnyValue)
             | AddRule (Clause AnyValue) [Clause AnyValue]
             | DumpFacts
             | DumpRules
             | Help
             deriving (Eq, Ord, Show)
