{-# LANGUAGE DeriveDataTypeable #-}
module Database.Datalog.Errors ( DatalogError(..) ) where

import Control.Exception
import Data.Text ( Text )
import Data.Typeable

import Database.Datalog.Relation

data DatalogError = SchemaError Relation
                  | RelationExistsError Text
                  | NoRelationError Relation
                  | MissingQueryError
                  | ExtraQueryError
                  | StratificationError
                  | RangeRestrictionViolation
                  | NonVariableInRuleHead
                  | NoVariableBinding Text
                  | UnexpectedNegatedLiteral
                  | UnexpectedConditionalClause
                  deriving (Typeable, Show)

instance Exception DatalogError
