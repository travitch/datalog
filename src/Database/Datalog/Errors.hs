{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeInType #-}
module Database.Datalog.Errors ( DatalogError(..) ) where

import Control.Exception
import Data.Kind ( Type )
import Data.Text ( Text )
import Data.Typeable

import qualified Database.Datalog.RelationSchema as DDR

data DatalogError k (r :: k -> Type ) = forall tps . SchemaError (DDR.RelationSchema r tps)
                  | RelationExistsError Text
                  | forall tps . NoRelationError (DDR.RelationSchema r tps)
                  | MissingQueryError
                  | ExtraQueryError
                  | StratificationError
                  | RangeRestrictionViolation
                  | NonVariableInRuleHead
                  | NoVariableBinding Text
                  | UnexpectedNegatedLiteral
                  | UnexpectedConditionalClause

deriving instance Show (DatalogError k r)

instance (Typeable k, Typeable r) => Exception (DatalogError k r)
