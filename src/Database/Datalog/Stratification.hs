{-# LANGUAGE FlexibleContexts #-}
module Database.Datalog.Stratification ( stratifyRules ) where

import Control.Failure
import Data.Hashable
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import Data.IntMap ( IntMap )
import qualified Data.IntMap as IM
import Data.Maybe ( fromJust )
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
  case any hasInternalNegation comps of
    True -> failure StratificationError
    False -> return $ IM.elems $ foldr (assignRule stratumNumbers) mempty rs
  where
    g = makeRuleDepGraph rs
    g' :: Gr [LNode RuleDepGraph] ()
    g' = condense g
    comps :: [[LNode RuleDepGraph]]
    comps = topsort' g'

    stratumNumbers :: HashMap Predicate Int
    stratumNumbers = foldr (computeStratumNumbers g) mempty comps

    hasInternalNegation :: [LNode RuleDepGraph] -> Bool
    hasInternalNegation ns =
      let nids = map unlabelNode ns
          allOutEdges = concatMap (lsuc g) nids
          negatedEdges = filter ((==DepNegated) . snd) allOutEdges
          internalNegatedEdges = filter ((`elem` nids) . fst) negatedEdges
      in null internalNegatedEdges

-- | Given the stratum number for each Predicate, place rules headed
-- with that Predicate in their respective strata.  This is
-- represented with an IntMap, which keeps the strata sorted.  This is
-- expanded into a different form by the caller.
assignRule :: HashMap Predicate Int -> Rule a -> IntMap [Rule a] -> IntMap [Rule a]
assignRule stratumNumbers r = IM.insertWith (++) snum [r]
  where
    headPred = adornedClausePredicate (ruleHead r)
    Just snum = HM.lookup headPred stratumNumbers

-- | Compute the stratum number for each 'Predicate'.  This requires a
-- fixed-point computation for each node in each SCC.  Nodes can get
-- different stratum numbers from other members of their SCC
--
-- The stratum number of a node N is the maximum number of negated
-- edges reachable from N in the RuleDepGraph.  Cycles with negations
-- on them are not allowed, so this is finite (infinite stratum
-- numbers imply that the query is not stratified).
computeStratumNumbers :: RuleDepGraph
                         -> [LNode RuleDepGraph]
                         -> HashMap Predicate Int
                         -> HashMap Predicate Int
computeStratumNumbers g c acc =
  let tbl' = foldr (computeStratumNumber g) acc c
  in case tbl' == acc of
    True -> acc
    False -> computeStratumNumbers g c tbl'

computeStratumNumber :: RuleDepGraph
                        -> LNode RuleDepGraph
                        -> HashMap Predicate Int
                        -> HashMap Predicate Int
computeStratumNumber g ln acc =
  HM.insert (nodeLabel ln) stratNum acc
  where
    nid = unlabelNode ln
    deps = lsuc g nid
    -- Add a zero as a default value if there are no dependencies
    -- (i.e., this is a leaf)
    stratNum = maximum $ 0 : map computeDepWeight deps
    computeDepWeight (depid, elbl)
      -- Self-loops contribute nothing (self loops on a negation are illegal)
      | depid == nid = 0
      -- Dependency weight not computed yet (in the same SCC).  It
      -- will be computed so just treat it as a zero for now and the
      -- fixed-point will take care of it.
      | not (HM.member (fromJust (lab g depid)) acc) = 0
      | otherwise =
        let Just snum = HM.lookup (fromJust (lab g depid)) acc
        in case elbl of
          DepNegated -> 1 + snum
          DepNormal -> snum

-- | Build a dependency graph between rules.  Each Predicate (goal
-- head) is a node in the graph.  There is an edge between the head
-- predicate and each body predicate.
--
-- Edges are labeled normal or negated.  If a body clause is negated,
-- the edge from the head to it is labeled DepNegated.
makeRuleDepGraph :: [Rule a] -> RuleDepGraph
makeRuleDepGraph rs = mkGraph ns es
  where
    preds = unique $ concatMap rulePredicates rs
    ns = zipWith LNode [0..] preds

    predToIdMap = HM.fromList $ zip preds [0..]
    predToId p = HM.lookupDefault (error "Missing predicate in predToIdMap") p predToIdMap

    es = foldr ruleToEdges [] rs
    -- | Make an edge from the predicate in the head of the rule to
    -- each predicate in the body.  The edge should have a DepNegated
    -- label if the clause is a negated clause.
    ruleToEdges r acc =
      let headPred = adornedClausePredicate (ruleHead r)
          src = predToId headPred
      in foldr (toEdge src) acc (ruleBody r)
    toEdge src bc acc =
      case bc of
        ConditionalClause _ _ -> acc
        NegatedLiteral (AdornedClause h _) ->
          LEdge (Edge src (predToId h)) DepNegated : acc
        Literal (AdornedClause h _) ->
          LEdge (Edge src (predToId h)) DepNormal : acc


unique :: (Hashable a, Eq a) => [a] -> [a]
unique = HS.toList . HS.fromList
