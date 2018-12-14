module Database.Datalog.Stratification ( stratifyRules ) where

import qualified Control.Monad.Catch as E
import qualified Data.Foldable as F
import           Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import           Data.HashSet ( HashSet )
import qualified Data.HashSet as HS
import           Data.IntMap ( IntMap )
import qualified Data.IntMap as IM
import           Data.Monoid
import           Data.Graph

import           Prelude

import           Database.Datalog.Database
import           Database.Datalog.Errors
import           Database.Datalog.Rules

-- | Stratify the input rules and magic rules; the rules should be
-- processed to a fixed-point in this order
stratifyRules :: (E.MonadThrow m) => [Rule a] -> m [[Rule a]]
stratifyRules rs =
  case all hasNoInternalNegation comps of
    False -> E.throwM StratificationError
    True -> return $ IM.elems $ foldr (assignRule stratumNumbers) mempty rs
  where
    (ctxts, negatedEdges) = makeRuleDependencies rs
    comps = stronglyConnCompR ctxts

    hasNoInternalNegation ns =
      case ns of
        AcyclicSCC _ -> True
        CyclicSCC vs ->
          let compNodes = HS.fromList $ map (\(_, x, _) -> x) vs
              internalEdges = foldr (isInternalEdge compNodes) mempty vs
          in HS.null $ HS.intersection internalEdges negatedEdges

    stratumNumbers = F.foldl' (computeStratumNumbers negatedEdges) mempty comps

isInternalEdge :: HashSet Relation -> Context -> HashSet (Relation, Relation) -> HashSet (Relation, Relation)
isInternalEdge compNodes (_, n, tgts) acc =
  acc `HS.union` HS.map (\t -> (n, t)) itgts
  where
    itgts = HS.fromList tgts `HS.intersection` compNodes

-- | Given the stratum number for each Relation, place rules headed
-- with that Relation in their respective strata.  This is
-- represented with an IntMap, which keeps the strata sorted.  This is
-- expanded into a different form by the caller.
assignRule :: HashMap Relation Int -> Rule a -> IntMap [Rule a] -> IntMap [Rule a]
assignRule stratumNumbers r = IM.insertWith (++) snum [r]
  where
    headPred = adornedClauseRelation (ruleHead r)
    Just snum = HM.lookup headPred stratumNumbers

-- | The stratum number of each member of an SCC will be the same
-- because all rules in an SCC depend on one another, and the stratum
-- number is the maximum number of negations reachable from a node.
-- since they all depend on one another and there can't be negations
-- within an SCC, all rules in an SCC must have the same stratum
-- number (which makes sense - all members of an SCC need to be
-- re-evaluated until a fixed-point is reached).  This makes the
-- stratum number computation easy - just take the maximum over all of
-- the rules in the SCC.
computeStratumNumber :: NegatedEdges -> HashMap Relation Int -> Context -> Int
computeStratumNumber negEdges m (_, r, deps) =
  case deps of
    -- If this relation has no dependencies, it is in stratum zero and
    -- can be evaluated first
    [] -> 0
    -- deps is not empty; if a dependency is not present it must be in
    -- this SCC and we can count it as zero because there are no
    -- intervening negations.
    deps' -> maximum $ map toStratNum deps'
  where
    toStratNum d =
      case HS.member (r, d) negEdges of
        True -> 1 + HM.lookupDefault 0 d m
        False -> HM.lookupDefault 0 d m


-- | Assign a stratum number to each SCC.  The stratum number is the
-- maximum number of negations reachable from a relation without
-- encountering a negation (negations within an SCC are impossible).
computeStratumNumbers :: NegatedEdges
                         -> HashMap Relation Int
                         -> SCC Context
                         -> HashMap Relation Int
computeStratumNumbers negEdges m comp =
  case comp of
    AcyclicSCC c@(r, _, _) -> HM.insert r (computeStratumNumber negEdges m c) m
    CyclicSCC cs ->
      -- The SCC can't be empty so maximum won't see an empty list
      let sn = maximum $ map (computeStratumNumber negEdges m) cs
      in foldr (\(r,_,_) acc -> HM.insert r sn acc) m cs

type NegatedEdges = HashSet (Relation, Relation)
type Context = (Relation, Relation, [Relation])

makeRuleDependencies :: [Rule a] -> ([Context], NegatedEdges)
makeRuleDependencies = toContexts . foldr addRuleDeps (mempty, mempty)
  where
    addRuleDeps (Rule (AdornedClause hrel _) b _) acc =
      foldr (addLitDeps hrel) acc b
    addLitDeps hrel l acc@(m, es) =
      case l of
        Literal (AdornedClause r _) ->
          (HM.insertWith HS.union hrel (HS.singleton r) m, es)
        NegatedLiteral (AdornedClause r _) ->
          (HM.insertWith HS.union hrel (HS.singleton r) m,
           HS.insert (hrel, r) es)
        ConditionalClause _ _ _ _ -> acc
    toContexts (dg, es) = (HM.foldrWithKey toContext [] dg, es)
    toContext hr brs acc = (hr, hr, HS.toList brs) : acc
