{-# LANGUAGE DeriveDataTypeable #-}
module Database.Datalog.Errors ( DatalogError(..) ) where

import Control.Exception
import Data.Parameterized.Some ( Some(..) )
import Data.Text ( Text )
import Data.Typeable

import qualified Database.Datalog.RelationSchema as DDR

data DatalogError r = SchemaError (Some (DDR.RelationSchema r))
                  | RelationExistsError Text
                  | NoRelationError (Some (DDR.RelationSchema r))
                  | MissingQueryError
                  | ExtraQueryError
                  | StratificationError
                  | RangeRestrictionViolation
                  | NonVariableInRuleHead
                  | NoVariableBinding Text
                  | UnexpectedNegatedLiteral
                  | UnexpectedConditionalClause
                  deriving (Show)

instance (Typeable r) => Exception (DatalogError r)
