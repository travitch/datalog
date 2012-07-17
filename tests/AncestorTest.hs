{-# LANGUAGE OverloadedStrings #-}
module Main ( main ) where

import Data.Set ( fromList )
import Data.Text ( Text )
import Test.Framework ( defaultMain, testGroup )
import Test.Framework.Providers.HUnit
import Test.HUnit

import Database.Datalog

main :: IO ()
main = defaultMain tests

tests = [ testGroup "t1" [ testCase "1" t1 ] ]

lit p ts = Literal $ Clause p ts

t1 = do
  res <- queryDatabase db1 q
  assertEqual "t1" expected (fromList res)
  where
    expected = fromList [ ["Mary", "John"]
                        , ["Joe", "John"]
                        , ["Bob", "John"]
                        , ["Sue", "John"]
                        ]
    Just db1 = makeDatabase $ do
      parentOf <- addRelation "parentOf" 2
      let facts :: [[Text]]
          facts = [ [ "Bob", "Mary" ]
                  , [ "Sue", "Mary" ]
                  , [ "Mary", "John" ]
                  , [ "Joe", "John" ]
                  ]
      mapM_ (assertFact parentOf) facts
    q = do
      parentOf <- relationPredicateFromName "parentOf"
      ancestorOf <- inferencePredicate "ancestorOf"
      let x = LogicVar "x"
          y = LogicVar "y"
          z = LogicVar "z"
      Clause ancestorOf [x, y] |- [ lit parentOf [x, y] ]
      Clause ancestorOf [x, y] |- [ lit parentOf [x, z], lit ancestorOf [z, y] ]
      issueQuery $ Clause ancestorOf [x, Atom "John" ]
