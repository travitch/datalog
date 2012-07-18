{-# LANGUAGE OverloadedStrings #-}
module Main ( main ) where

import Data.Set ( fromList )
import Data.Text ( Text )
import Test.Framework ( defaultMain, testGroup, Test )
import Test.Framework.Providers.HUnit
import Test.HUnit hiding ( Test )

import Database.Datalog

main :: IO ()
main = defaultMain tests

tests :: [Test]
tests = [ testGroup "t1" [ testCase "1" t1
                         , testCase "2" t2
                         , testCase "3" t3
                         , testCase "4" t4
                         ] ]

lit p ts = Literal $ Clause p ts

db1 :: Maybe (Database Text)
db1 = makeDatabase $ do
      parentOf <- addRelation "parentOf" 2
      let facts :: [[Text]]
          facts = [ [ "Bob", "Mary" ]
                  , [ "Sue", "Mary" ]
                  , [ "Mary", "John" ]
                  , [ "Joe", "John" ]
                  ]
      mapM_ (assertFact parentOf) facts

t1 = do
  let Just db = db1
  res <- queryDatabase db q
  assertEqual "t1" expected (fromList res)
  where
    expected = fromList [ ["Mary", "John"]
                        , ["Joe", "John"]
                        , ["Bob", "John"]
                        , ["Sue", "John"]
                        ]
    q = do
      parentOf <- relationPredicateFromName "parentOf"
      ancestorOf <- inferencePredicate "ancestorOf"
      let x = LogicVar "x"
          y = LogicVar "y"
          z = LogicVar "z"
      Clause ancestorOf [x, y] |- [ lit parentOf [x, y] ]
      Clause ancestorOf [x, y] |- [ lit parentOf [x, z], lit ancestorOf [z, y] ]
      issueQuery $ Clause ancestorOf [x, Atom "John" ]

t2 = do
  let Just db = db1
  res <- queryDatabase db q
  assertEqual "t2" expected (fromList res)
  where
    expected = fromList [ ["Bob", "Mary"]
                        , ["Sue", "Mary"]
                        ]
    q = do
      parentOf <- relationPredicateFromName "parentOf"
      ancestorOf <- inferencePredicate "ancestorOf"
      let x = LogicVar "x"
          y = LogicVar "y"
          z = LogicVar "z"
      Clause ancestorOf [x, y] |- [ lit parentOf [x, y] ]
      Clause ancestorOf [x, y] |- [ lit parentOf [x, z], lit ancestorOf [z, y] ]
      issueQuery $ Clause ancestorOf [x, Atom "Mary" ]

t3 = do
  let Just db = db1
  res <- queryDatabase db q
  assertEqual "t3" expected (fromList res)
  where
    expected = fromList [ ["Sue", "John"]
                        , ["Sue", "Mary"]
                        ]
    q = do
      parentOf <- relationPredicateFromName "parentOf"
      ancestorOf <- inferencePredicate "ancestorOf"
      let x = LogicVar "x"
          y = LogicVar "y"
          z = LogicVar "z"
      Clause ancestorOf [x, y] |- [ lit parentOf [x, y] ]
      Clause ancestorOf [x, y] |- [ lit parentOf [x, z], lit ancestorOf [z, y] ]
      issueQuery $ Clause ancestorOf [Atom "Sue", x ]

t4 = do
  let Just db = db1
  res <- queryDatabase db q
  assertEqual "t4" expected (fromList res)
  where
    expected = fromList []
    q = do
      parentOf <- relationPredicateFromName "parentOf"
      ancestorOf <- inferencePredicate "ancestorOf"
      let x = LogicVar "x"
          y = LogicVar "y"
          z = LogicVar "z"
      Clause ancestorOf [x, y] |- [ lit parentOf [x, y] ]
      Clause ancestorOf [x, y] |- [ lit parentOf [x, z], lit ancestorOf [z, y] ]
      issueQuery $ Clause ancestorOf [x, Atom "Bob"]
