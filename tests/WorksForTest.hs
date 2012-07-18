{-# LANGUAGE OverloadedStrings #-}
module Main ( main ) where

import Data.Hashable
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
                         -- , testCase "3" t3
                         -- , testCase "4" t4
                         ] ]

data WorkInfo = EID !Int -- id
              | EN !Text -- Name
              | EP !Text -- Position
              | J !Text  -- Job
              deriving (Eq, Ord, Show)

instance Hashable WorkInfo where
  hash (EID i) = 1 `combine` hash i
  hash (EN n) = 2 `combine` hash n
  hash (EP p) = 3 `combine` hash p
  hash (J j) = 4 `combine` hash j

db1 :: Maybe (Database WorkInfo)
db1 = makeDatabase $ do
  employee <- addRelation "employee" 3
  let emplFacts = [ [ EID 1, EN "Bob", EP "Boss" ]
                  , [ EID 2, EN "Mary", EP "Chief Accountant"]
                  , [ EID 3, EN "John", EP "Accountant" ]
                  , [ EID 4, EN "Sameer", EP "Chief Programmer" ]
                  , [ EID 5, EN "Lilian", EP "Programmer" ]
                  , [ EID 6, EN "Li", EP "Technician" ]
                  , [ EID 7, EN "Fred", EP "Sales" ]
                  , [ EID 8, EN "Brenda", EP "Sales" ]
                  , [ EID 9, EN "Miki", EP "Project Management" ]
                  , [ EID 10, EN "Albert", EP "Technician" ]
                  ]
  mapM_ (assertFact employee) emplFacts

  bossOf <- addRelation "bossOf" 2
  let bossFacts = [ [ EID 1, EID 2 ]
                  , [ EID 2, EID 3 ]
                  , [ EID 1, EID 4 ]
                  , [ EID 4, EID 5 ]
                  , [ EID 4, EID 6 ]
                  , [ EID 1, EID 7 ]
                  , [ EID 7, EID 8 ]
                  , [ EID 1, EID 9 ]
                  , [ EID 6, EID 10 ]
                  ]
  mapM_ (assertFact bossOf) bossFacts

  canDo <- addRelation "canDo" 2
  let canDoFacts = [ [ EP "Boss", J "Management" ]
                   , [ EP "Accountant", J "Accounting"  ]
                   , [ EP "Chief Accountant", J "Accounting" ]
                   , [ EP "Programmer", J "Programming" ]
                   , [ EP "Chief Programmer", J "Programming" ]
                   , [ EP "Technician", J "Server Support" ]
                   , [ EP "Sales", J "Sales" ]
                   , [ EP "Project Management", J "Project Management" ]
                   ]
  mapM_ (assertFact canDo) canDoFacts

  jobCanBeDoneBy <- addRelation "jobCanBeDoneBy" 2
  let replaceFacts = [ [ J "PC Support", J "Server Support" ]
                     , [ J "PC Support", J "Programming" ]
                     , [ J "Payroll", J "Accounting" ]
                     ]
  mapM_ (assertFact jobCanBeDoneBy) replaceFacts

  jobExceptions <- addRelation "jobExceptions" 2
  assertFact jobExceptions [ EID 4, J "PC Support" ]

q1 = do
  employee <- relationPredicateFromName "employee"
  bossOf <- relationPredicateFromName "bossOf"
  worksFor <- inferencePredicate "worksFor"
  let x = LogicVar "X"
      y = LogicVar "Y"
      z = LogicVar "Z"
      eid = LogicVar "E-ID"
      bid = LogicVar "B-ID"
  (worksFor, [x, y]) |- [ lit bossOf [bid, eid]
                        , lit employee [eid, x, Anything]
                        , lit employee [bid, y, Anything]
                        ]
  (worksFor, [x, y]) |- [ lit worksFor [x, z]
                        , lit worksFor [z, y]
                        ]
  issueQuery worksFor [ BindVar "name", x ]

t1 :: Assertion
t1 = do
  let Just db = db1
      Just qp = buildQueryPlan db q1

  res <- executeQueryPlan qp db [("name", EN "Albert")]
  assertEqual "t1" expected (fromList res)
  where
    expected = fromList [ [EN "Albert", EN "Li"]
                        , [EN "Albert", EN "Sameer"]
                        , [EN "Albert", EN "Bob"]
                        ]
t2 :: Assertion
t2 = do
  let Just db = db1
      Just qp = buildQueryPlan db q1

  res <- executeQueryPlan qp db [("name", EN "Lilian")]
  assertEqual "t1" expected (fromList res)
  where
    expected = fromList [ [EN "Lilian", EN "Sameer"]
                        , [EN "Lilian", EN "Bob"]
                        ]




{-
t1 :: Assertion
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
      (ancestorOf, [x, y]) |- [ lit parentOf [x, y] ]
      (ancestorOf, [x, y]) |- [ lit parentOf [x, z], lit ancestorOf [z, y] ]
      issueQuery ancestorOf [x, Atom "John" ]

t2 :: Assertion
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
      (ancestorOf, [x, y]) |- [ lit parentOf [x, y] ]
      (ancestorOf, [x, y]) |- [ lit parentOf [x, z], lit ancestorOf [z, y] ]
      issueQuery ancestorOf [x, Atom "Mary" ]

t3 :: Assertion
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
      (ancestorOf, [x, y]) |- [ lit parentOf [x, y] ]
      (ancestorOf, [x, y]) |- [ lit parentOf [x, z], lit ancestorOf [z, y] ]
      issueQuery ancestorOf [Atom "Sue", x ]

t4 :: Assertion
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
      (ancestorOf, [x, y]) |- [ lit parentOf [x, y] ]
      (ancestorOf, [x, y]) |- [ lit parentOf [x, z], lit ancestorOf [z, y] ]
      issueQuery ancestorOf [x, Atom "Bob"]
-}
