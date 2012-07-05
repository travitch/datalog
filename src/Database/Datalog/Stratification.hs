{-# LANGUAGE FlexibleContexts #-}
module Database.Datalog.Stratification ( stratifyRules ) where

import Control.Failure
import Data.Hashable
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import Data.Monoid

import Data.Graph.Interface
import Data.Graph.LazyHAMT
import Data.Graph.Algorithms.Matching.DFS

import Database.Datalog.Database
import Database.Datalog.Errors
import Database.Datalog.Rules


data RuleDep = DepNormal | DepNegated
             deriving (Eq, Ord)
type RuleDepGraph = Gr Predicate RuleDep


-- | Stratify the input rules and magic rules; the rules should be
-- processed to a fixed-point in this order
stratifyRules :: (Failure DatalogError m) => [Rule a] -> m [[Rule a]]
stratifyRules rs =
  -- Visit the graph bottom-up (from the leaves) and assign stratum
  -- numbers on the fly.
  case any hasInternalNegation comps of
    True -> failure StratificationError
    False -> undefined
  where
    (g, predToId, predFromId) = makeRuleDepGraph rs
    g' :: Gr [LNode RuleDepGraph] ()
    g' = condense g
    comps :: [[LNode RuleDepGraph]]
    comps = topsort' g'

    stratumNumbers :: HashMap Predicate Int
    stratumNumbers = foldr computeStratumNumber mempty comps

    hasInternalNegation :: [LNode RuleDepGraph] -> Bool
    hasInternalNegation ns =
      let nids = map unlabelNode ns
          allOutEdges = concatMap (lsuc g) nids
          negatedEdges = filter ((==DepNegated) . snd) allOutEdges
          internalNegatedEdges = filter ((`elem` nids) . fst) negatedEdges
      in null internalNegatedEdges

computeStratumNumber = undefined

makeRuleDepGraph :: [Rule a] -> (RuleDepGraph, Predicate -> Int, Int -> Predicate)
makeRuleDepGraph rs = (mkGraph ns es, predToId, predFromId)
  where
    preds = unique $ concatMap rulePredicates rs
    ns = zipWith LNode [0..] preds

    predToIdMap = HM.fromList $ zip preds [0..]
    predToId p = HM.lookupDefault (error "Missing predicate in predToIdMap") p predToIdMap

    predFromIdMap = HM.fromList $ zip [0..] preds
    predFromId p = HM.lookupDefault (error "Missing predicate in predFromIdMap") p predFromIdMap

    es = foldr ruleToEdges [] rs
    -- | Make an edge from the predicate in the head of the rule to
    -- each predicate in the body.  The edge should have a DepNegated
    -- label if the clause is a negated clause.
    ruleToEdges r acc =
      let headPred = clausePredicate (ruleHead r)
          src = predToId headPred
      in foldr (toEdge src) acc (ruleBody r)
    toEdge src bc acc =
      case bc of
        ConditionalClause _ _ -> acc
        NegatedClause (Clause h _) ->
          LEdge (Edge src (predToId h)) DepNegated : acc
        BodyClause (Clause h _) ->
          LEdge (Edge src (predToId h)) DepNormal : acc


unique :: (Hashable a, Eq a) => [a] -> [a]
unique = HS.toList . HS.fromList