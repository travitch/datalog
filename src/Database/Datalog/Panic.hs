{-# LANGUAGE TemplateHaskell #-}
module Database.Datalog.Panic (
  Datalog(..),
  P.panic
  ) where

import qualified Panic as P

data Datalog = DatalogCore
             | DatalogEvaluator
             deriving (Show)

instance P.PanicComponent Datalog where
  panicComponentName c = show c
  panicComponentIssues _ = "https://github.com/travitch/datalog/issues"
  panicComponentRevision = $(P.useGitRevision)
