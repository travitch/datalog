{-# LANGUAGE DeriveDataTypeable #-}
module Database.Datalog.Errors ( DatalogError(..) ) where

import Control.Exception
import Data.Text ( Text )
import Data.Typeable

data DatalogError = SchemaError Text
                  | RelationExistsError Text
                  | NoRelationError Text
                  | MissingQueryError
                  | ExtraQueryError
                  | StratificationError
                  | RangeRestrictionViolation
                  | NonVariableInRuleHead
                  deriving (Typeable, Show)

instance Exception DatalogError
