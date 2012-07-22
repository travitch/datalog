{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}
module Main ( main ) where

import Control.Monad ( forM_ )
import Data.List ( sort )
import qualified Data.Set as S
import Test.Framework ( defaultMain, testGroup, Test )
import Test.Framework.Providers.HUnit
import Test.HUnit hiding ( Test )

import Database.Datalog

main :: IO ()
main = defaultMain tests

tests :: [Test]
tests = [ testGroup "t1" [ testCase "4queens" t4
                         , testCase "5queens" t5
                         ] ]

type Position = (Int, Int)

dbN :: (Failure DatalogError m) => Int -> m (Database Position)
dbN n = makeDatabase $ do
  let posTuples = [ (x, y) | x <- [1..n], y <- [1..n] ]
  position <- addRelation "position" 1
  forM_ posTuples $ \(x, y) -> assertFact position [ (x, y) ]

-- Note, the restrictions on x and y equality also imply that the
-- position rule can't select the same position more than once in a
-- solution
posCanAttack :: Position -> Position -> Bool
posCanAttack (x1, y1) (x2, y2) =
  x1 == x2 || y1 == y2 || (abs (x1 - x2) == abs (y1 - y2))

unique :: [[Position]] -> [[Position]]
unique = S.toList . S.fromList

-- Return False if any position can attack any others
noneCanAttack :: [Position] -> Bool
noneCanAttack [] = True
noneCanAttack [_] = True
noneCanAttack (p:ps) = not (any (posCanAttack p) ps) && noneCanAttack ps

t4 :: Assertion
t4 = do
  db4 <- dbN 4
  res <- queryDatabase db4 q
  let res' = unique $ map sort res
  print res'
  assertBool "t4" $ all noneCanAttack res' && length res' == 2
  where
    q = do
      position <- relationPredicateFromName "position"
      canAttack <- inferencePredicate "canAttack"
      let x = LogicVar "X"
          y = LogicVar "Y"
      (canAttack, [x, y]) |- [ lit position [x]
                             , lit position [y]
                             , cond2 posCanAttack (x, y)
                             ]
      let p1 = LogicVar "P1"
          p2 = LogicVar "P2"
          p3 = LogicVar "P3"
          p4 = LogicVar "P4"
      queens <- inferencePredicate "queens"
      (queens, [p1, p2, p3, p4]) |- [ lit position [p1]
                                    , lit position [p2]
                                    , lit position [p3]
                                    , lit position [p4]
                                    , negLit canAttack [p1, p2]
                                    , negLit canAttack [p1, p3]
                                    , negLit canAttack [p1, p4]
                                    , negLit canAttack [p2, p3]
                                    , negLit canAttack [p2, p4]
                                    , negLit canAttack [p3, p4]
                                    ]
      issueQuery queens [p1, p2, p3, p4]

t5 :: Assertion
t5 = do
  db5 <- dbN 5
  res <- queryDatabase db5 q
  let res' = unique $ map sort res
  print res'
  assertBool "t5" $ all noneCanAttack res' && length res' == 10
  where
    q = do
      position <- relationPredicateFromName "position"
      canAttack <- inferencePredicate "canAttack"
      let x = LogicVar "X"
          y = LogicVar "Y"
      (canAttack, [x, y]) |- [ lit position [x]
                             , lit position [y]
                             , cond2 posCanAttack (x, y)
                             ]
      let p1 = LogicVar "P1"
          p2 = LogicVar "P2"
          p3 = LogicVar "P3"
          p4 = LogicVar "P4"
          p5 = LogicVar "P5"
      queens <- inferencePredicate "queens"
      (queens, [p1, p2, p3, p4, p5]) |- [ lit position [p1]
                                        , lit position [p2]
                                        , lit position [p3]
                                        , lit position [p4]
                                        , lit position [p5]
                                        , negLit canAttack [p1, p2]
                                        , negLit canAttack [p1, p3]
                                        , negLit canAttack [p1, p4]
                                        , negLit canAttack [p1, p5]
                                        , negLit canAttack [p2, p3]
                                        , negLit canAttack [p2, p4]
                                        , negLit canAttack [p2, p5]
                                        , negLit canAttack [p3, p4]
                                        , negLit canAttack [p3, p5]
                                        , negLit canAttack [p4, p5]
                                        ]
      issueQuery queens [p1, p2, p3, p4, p5]
