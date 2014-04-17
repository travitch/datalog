{-# LANGUAGE BangPatterns, ScopedTypeVariables #-}
-- | This module defines the evaluation strategy of the library.
--
-- It currently uses a bottom-up semi-naive evaluator.
module Database.Datalog.Evaluate (
  applyRuleSet,
  select
  ) where

import Control.Applicative
import qualified Control.Monad.Catch as E
import Control.Monad ( foldM, liftM )
import Control.Monad.ST.Strict
import Data.Graph
import Data.Hashable
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import Data.Maybe ( fromMaybe )
import Data.Monoid
import Data.Vector.Mutable ( STVector )
import qualified Data.Vector.Mutable as V

import Database.Datalog.Database
import Database.Datalog.Errors
import Database.Datalog.Rules

import Debug.Trace
debug = flip trace

-- | Bindings are vectors of values.  Each variable in a rule is
-- assigned an index in the Bindings during the adornment process.
-- When evaluating a rule, if a free variable is encountered, all of
-- its possible values are entered at the index for that variable in a
-- Bindings vector.  When a bound variable is encountered, its current
-- value is looked up from the Bindings.  If that value does not match
-- the concrete tuple being examined, that tuple is rejected.
--
-- The mapping of variable to index into the bindings vector is stored
-- in the Rule data structure.
newtype Bindings s a = Bindings (STVector s a)


-- | Apply a set of rules.  All of the rules must have the same head
-- relation.  This is what implements the semi-naive evaluation
-- strategy.  For each rule of the form
--
-- > T(x,y) |- G(x,z), T(z,y).
--
-- simulate the rule
--
-- > ΔT(x,y) |- G(x,z), ΔT(z,y).
--
-- That is, at each step only look at the *new* tuples for each
-- recursive relation.  The intuition is that, if a new tuple is to be
-- generated on the next step, it must reference a new tuple from this
-- step (otherwise it would have already been generated) If a relation
-- appears twice in a body:
--
-- > T(x,y) |- T(x,z), T(z,y).
--
-- we have to substitute ΔT once for *each* occurrence of T in the
-- body, with the other occurrences referencing the non-Δ table:
--
-- > ΔT(x,y) |- ΔT(x,z), T(z,y).
-- > ΔT(x,y) |- T(x,z), ΔT(z,y).
--
-- While collecting all of the new tuples (see projectLiteral), a new
-- Δ table is generated.
applyRuleSet :: (E.MonadThrow m, Eq a, Hashable a, Show a)
                => Database a -> [Rule a] -> m (Database a)
applyRuleSet _ [] = error "applyRuleSet: Empty rule set not possible"
applyRuleSet db rss@(r:_) = return $ runST $ do
  bss <- concat <$> mapM (applyRules db) (orderRules rss)
  db' <- projectLiterals db h bss
  return db' -- `debug` show db'
  where
    h = ruleHead r

-- | Each of the lists of generated bindings has its own
-- ruleVariableMap, so zip them together so that project has them
-- paired up and ready to use.
--
-- Apply a set of rules
applyRules :: (Eq a, Hashable a, Show a)
              => Database a
              -> [Rule a]
              -> ST s [(Rule a, [Bindings s a])]
applyRules db rs = do
  bs <- mapM (applyRule db) rs
  return $ zip rs bs

-- | Toplogically sort rules (with SCCs treated as a unit).  This
-- means that dependency rules will be fired before the rules that
-- depend on them, which is the best evaluation order we can hope for.
orderRules :: forall a . (Eq a, Hashable a) => [Rule a] -> [[Rule a]]
orderRules rs = map toList (stronglyConnComp deps)
  where
    toList (AcyclicSCC r) = [r]
    toList (CyclicSCC rss) = rss
    toKeyM = HM.fromList (zip rs [0..])
    toKey :: Rule a -> Int
    toKey r = fromMaybe (error "Missing toKeyM entry") $ HM.lookup r toKeyM

    deps = foldr toContext [] rs
    toContext r@(Rule _ b _) acc =
      -- All of the rules for a given relation are in the same SCC
      -- stratum, so we will see them all in @rs@
      let brules = concatMap relationToRules b
      in (r, toKey r, map toKey brules) : acc
    relationToRules rel = filter (hasRelHead rel) rs
    hasRelHead c (Rule h _ _) =
      case c of
        Literal ac -> adornedClauseRelation h == adornedClauseRelation ac
        -- This should probably be impossible since negated terms
        -- would be in a different stratum.
        NegatedLiteral ac -> adornedClauseRelation h == adornedClauseRelation ac
        _ -> False

-- | A worker to apply a single rule to the database (producing a new
-- database).  This handles deciding if we need to do any Δ-table
-- substitutions.  If not, it just does a simple fold with
-- joinLiteral.
applyRule :: (Eq a, Hashable a, Show a)
             => Database a -> Rule a -> ST s [Bindings s a]
applyRule db r = do
  -- We need to substitute the ΔT table in for *one* occurrence of the
  -- T relation in the rule body at a time.  It must be substituted in
  -- at *each* position where T appears.
  case any (referencesRelation hr) b of
    -- If the relation does not appear in the body at all, we don't
    -- need to do the delta substitution.
    False -> do
      v0 <- V.new (HM.size m)
      foldM (joinLiteral db) [Bindings v0] b
    -- Otherwise, swap the delta table in for each each occurrence of
    -- the relation in the body.
    True -> concat <$> foldM (joinWithDeltaAt db hr b m) [] b
  where
    h = ruleHead r
    hr = adornedClauseRelation h
    b = ruleBody r
    m = ruleVariableMap r

-- | Return True if the given literal references the given Relation
referencesRelation:: Relation -> Literal AdornedClause a -> Bool
referencesRelation hrel rel =
  case rel of
    Literal l -> adornedClauseRelation l == hrel
    NegatedLiteral l -> adornedClauseRelation l == hrel
    _ -> False

-- | The worker that substitutes a Δ-table for each clause referencing
-- the relation @hr@.
joinWithDeltaAt :: (Eq a, Hashable a)
                   => Database a
                   -> Relation
                   -> [Literal AdornedClause a]
                   -> HashMap k v
                   -> [[Bindings s a]]
                   -> Literal AdornedClause a
                   -> ST s [[Bindings s a]]
joinWithDeltaAt db hr b m acc c =
  case referencesRelation hr c of
    -- This clause doesn't reference the relation so don't do anything
    False -> return acc
    -- This clause does reference it, so we need to evaluate the
    -- entire rule here.  swapJoin handles substituting the Δ table
    -- for the relation in this clause (see withDeltaRelation - it
    -- makes a new database with the Δ swapped for the data of this
    -- relation).
    True -> do
      v0 <- V.new (HM.size m)
      bs <- foldM swapJoin [Bindings v0] b
      return (bs : acc)
  where
    swapJoin bs thisClause =
      case thisClause == c of
        False -> joinLiteral db bs thisClause
        True -> withDeltaRelation db hr $ \db' -> joinLiteral db' bs thisClause

-- | Ensure that the relation named by the clause argument is in the
-- database.  Get the DBRelation.  Then fold over the Bindings,
-- constructing a tuple for each one (that is inserted into the
-- relation).  Then build a new database with that relation replaced
-- with the new one.
projectLiterals :: (Eq a, Hashable a, Show a)
                   => Database a
                   -> AdornedClause a
                   -> [(Rule a, [Bindings s a])]
                   -> ST s (Database a)
projectLiterals db c bssMaps = do
  let r = adornedClauseRelation c
      rel = ensureDatabaseRelation db r (length (adornedClauseTerms c))
      rel' = resetRelationDelta rel
  -- We reset the delta since we are computing the new delta for the
  -- next iteration.  The act of adding tuples to the relation
  -- automatically computes the delta.
  rel'' <- foldM (\irel (rule, bs) -> foldM (project rule) irel bs) rel' bssMaps
  return $ replaceRelation db rel''
  where
    project rule !r b = do
      t <- bindingsToTuple (ruleHead rule) (ruleVariableMap rule) b
      return $ addTupleToRelation r t

-- | Determine if a PartialTuple and a concrete Tuple from the
-- database match.  Walks the partial tuple (which is sorted by index)
-- and the current tuple in parallel and tries to avoid allocations as
-- much as possible.
tupleMatches :: (Eq a) => PartialTuple a -> Tuple a -> Bool
tupleMatches (PartialTuple pvs) (Tuple vs) =
  parallelTupleWalk pvs vs

parallelTupleWalk :: (Eq a) => [Maybe a] -> [a] -> Bool
parallelTupleWalk [] [] = True
parallelTupleWalk (p:ps) (v:vs) =
  case p of
    Nothing -> parallelTupleWalk ps vs
    Just pv -> pv == v && parallelTupleWalk ps vs
parallelTupleWalk _ _ = error "Partial tuple length mismatch"

{-# INLINE scanSpace #-}
-- | The common worker for 'select' and 'matchAny'
scanSpace :: (Eq a)
             => ((Tuple a -> Bool) -> [Tuple a] -> b)
             -> Database a
             -> Relation
             -> PartialTuple a
             -> b
scanSpace f db p pt = f (tupleMatches pt) space
  where
    -- FIXME: This is where we use the index, if available.  If not,
    -- we have to fall back to a table scan.  Instead of computing
    -- indices up front, it may be best to only compute them on the
    -- fly (and then only if they will be referenced again later).
    -- They can be thrown away as soon as they can't be referenced
    -- again.  This will save storage and up-front costs.

    -- Note that the relation might not exist in the database here
    -- because this is the first time data is being inferred for the
    -- EDB.  In that case, just start with empty data and the project
    -- step will insert the table into the database for the next step.
    space = fromMaybe mempty (dataForRelation db p)

-- | Return all of the tuples in the given relation that match the
-- given PartialTuple
select :: (Eq a) => Database a -> Relation -> PartialTuple a -> [Tuple a]
select = scanSpace filter

-- | Return true if any tuples in the given relation match the given
-- 'PartialTuple'
anyMatch :: (Eq a) => Database a -> Relation -> PartialTuple a -> Bool
anyMatch = scanSpace any

{-# INLINE joinLiteralWith #-}
-- | The common worker for the non-conditional clause join functions.
joinLiteralWith :: AdornedClause a
                   -> [Bindings s a]
                   -> (Bindings s a -> PartialTuple a -> ST s [Bindings s a])
                   -> ST s [Bindings s a]
joinLiteralWith c bs f = concatMapM (apply c f) bs
  where
    apply cl fn b = do
      pt <- buildPartialTuple cl b
      fn b pt

-- | Join a literal with the current set of bindings.  This can
-- increase the number of bindings (for a non-negated clause) or
-- decrease the number of bindings (for a negated or conditional
-- clause).
joinLiteral :: (Eq a, Hashable a)
               => Database a
               -> [Bindings s a]
               -> Literal AdornedClause a
               -> ST s [Bindings s a]
joinLiteral db bs (Literal c) = joinLiteralWith c bs (normalJoin db c)
joinLiteral db bs (NegatedLiteral c) = joinLiteralWith c bs (negatedJoin db c)
joinLiteral _ bs (ConditionalClause _ p vs m) =
  foldM (applyJoinCondition p vs m) [] bs

-- | Extract the values that the predicate requires from the current
-- bindings.  Apply the predicate and if it returns True, retain the
-- set of bindings; otherwise, discard it.
applyJoinCondition :: (Eq a, Hashable a)
                      => ([a] -> Bool)
                      -> [Term a]
                      -> HashMap (Term a) Int
                      -> [Bindings s a]
                      -> Bindings s a
                      -> ST s [Bindings s a]
applyJoinCondition p vs m acc b@(Bindings binds) = do
  vals <- mapM extractBinding vs
  case p vals of
    True -> return $! b : acc
    False -> return acc
  where
    extractBinding t =
      let Just ix = HM.lookup t m
      in V.read binds ix

-- | Non-negated join; it works by selecting all of the tuples
-- matching the input PartialTuple and then recording all of the newly
-- bound variable values (i.e., the free variables in the rule).  This
-- produces one set of bindings for each possible value of the free
-- variables in the rule (or could be empty if there are no matching
-- tuples).
normalJoin :: (Eq a, Hashable a) => Database a -> AdornedClause a -> Bindings s a
              -> PartialTuple a -> ST s [Bindings s a]
normalJoin db c binds pt = mapM (projectTupleOntoLiteral c binds) ts
  where
    ts = select db (adornedClauseRelation c) pt

-- | Retain the input binding if there are no matches in the database
-- for the input PartialTuple.  Otherwise reject it.
negatedJoin :: (Eq a, Hashable a) => Database a -> AdornedClause a -> Bindings s a
               -> PartialTuple a -> ST s [Bindings s a]
negatedJoin db c binds pt =
  case anyMatch db (adornedClauseRelation c) pt of
    True -> return []
    False -> return [binds]

-- | For each term in the clause, take it as a literal if it is bound
-- or is an atom.  Otherwise, leave it as free (not mentioned in the
-- partial tuple).
buildPartialTuple :: AdornedClause a -> Bindings s a -> ST s (PartialTuple a)
buildPartialTuple c (Bindings bs) =
  PartialTuple <$> mapM toPartial (adornedClauseTerms c)
  where
    toPartial ta =
      case ta of
        (Atom a, BoundAtom) -> return $! Just a
        (_, Bound slot) -> do
          b <- V.read bs slot
          return $! Just b
        _ -> return Nothing


-- | For each free variable in the tuple (according to the adorned
-- clause), enter its value into the input bindings
projectTupleOntoLiteral :: AdornedClause a -> Bindings s a -> Tuple a -> ST s (Bindings s a)
projectTupleOntoLiteral c (Bindings binds) (Tuple t) = do
  -- We need a copy here because the input bindings are shared among
  -- many calls to this function
  b <- V.clone binds
  let atoms = zip (adornedClauseTerms c) t
  mapM_ (bindFreeVariable b) atoms
  return $! Bindings b
  where
    bindFreeVariable b ((_, adornment), val) =
      case adornment of
        Free ix -> V.write b ix val
        _ -> return ()

-- | Convert a set of variable bindings to a tuple that matches the
-- input clause (which should have all variables).  This is basically
-- unifying variables with the head of the rule.
bindingsToTuple :: (Eq a, Hashable a, Show a)
                   => AdornedClause a
                   -> HashMap (Term a) Int
                   -> Bindings s a
                   -> ST s (Tuple a)
bindingsToTuple c vmap (Bindings bs) = do
  vals <- mapM variableTermToValue (adornedClauseTerms c)
  return $ Tuple vals
  where
    variableTermToValue (t, _) =
      case HM.lookup t vmap of
        Nothing -> error ("NonVariableInRuleHead " ++ show c ++ " " ++ show t ++ " " ++ show vmap)
        Just ix -> V.read bs ix


-- Helpers

{-# INLINE mapM' #-}
-- | This is an alternative definition of mapM that accumulates its
-- results on the heap instead of the stack.  This should avoid some
-- stack overflows when processing some million+ element lists..
mapM' :: (Monad m) => (a -> m b) -> [a] -> m [b]
mapM' f = go []
  where
    go acc [] = return (reverse acc)
    go acc (a:as) = do
      x <- f a
      go (x:acc) as

{-# INLINE concatMapM #-}
concatMapM :: (Monad m) => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = liftM concat (mapM' f xs)
