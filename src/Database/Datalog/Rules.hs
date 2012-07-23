{-# LANGUAGE FlexibleContexts, BangPatterns #-}
-- | FIXME: Change the adornment/query building process such that
-- conditional clauses are always processed last.  This is necessary
-- so that all variables are bound.
--
-- FIXME: Add an assertion to say that ConditionalClauses cannot have
-- Free variables.
module Database.Datalog.Rules (
  Adornment(..),
  Term(LogicVar, BindVar, Anything, Atom),
  Clause,
  AdornedClause(..),
  Rule(..),
  Literal(..),
  Query,
  QueryBuilder,
  PartialTuple,
  (|-),
  assertRule,
  relationPredicateFromName,
  inferencePredicate,
  ruleRelations,
  issueQuery,
  applyRule,
  runQuery,
  select,
  queryToPartialTuple,
  queryPredicate,
  lit,
  negLit,
  cond1,
  cond2,
  cond3,
  cond4,
  cond5,
  bindQuery
  ) where

import Control.Applicative
import Control.Failure
import Control.Monad.State.Strict
import Control.Monad.ST.Strict
import Data.Hashable
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import Data.List ( intercalate )
import Data.Maybe ( fromMaybe, mapMaybe )
import Data.Monoid
import Data.Text ( Text )
import qualified Data.Text as T
import Data.Vector.Mutable ( STVector )
import qualified Data.Vector.Mutable as V
import Text.Printf

import Database.Datalog.Errors
import Database.Datalog.Database

data QueryState a = QueryState { intensionalDatabase :: Database a
                               , queryRules :: [(Clause a, [Literal Clause a])]
                               }

-- | The Monad in which queries are constructed and rules are declared
type QueryBuilder m a = StateT (QueryState a) m


data Term a = LogicVar !Text
              -- ^ A basic logic variable.  Equality is based on the
              -- variable name.
            | BindVar !Text
              -- ^ A special variable available in queries that can be
              -- bound at query execution time
            | Anything
              -- ^ A term that is allowed to take any value (this is
              -- sugar for a fresh logic variable)
            | Atom a
              -- ^ A user-provided literal from the domain a
            | FreshVar !Int
              -- ^ A fresh logic variable, generated internally for
              -- each Anything occurrence.  Not exposed to the user

instance (Show a) => Show (Term a) where
  show (LogicVar t) = T.unpack t
  show (BindVar t) = "??" ++ T.unpack t
  show (Atom a) = show a
  show Anything = "*"
  show (FreshVar _) = "*"

instance (Hashable a) => Hashable (Term a) where
  hash (LogicVar t) = hash t `combine` 1
  hash (BindVar t) = hash t `combine` 2
  hash (Atom a) = hash a
  hash Anything = 99
  hash (FreshVar i) = 22 `combine` hash i

instance (Eq a) => Eq (Term a) where
  (LogicVar t1) == (LogicVar t2) = t1 == t2
  (BindVar t1) == (BindVar t2) = t1 == t2
  (Atom a1) == (Atom a2) = a1 == a2
  Anything == Anything = True
  FreshVar i1 == FreshVar i2 = i1 == i2
  _ == _ = False

data Clause a = Clause { clauseRelation :: Relation
                       , clauseTerms :: [Term a]
                       }

instance (Show a) => Show (Clause a) where
  show (Clause p ts) =
    printf "%s(%s)" (show p) (intercalate ", " (map show ts))

data Adornment = Free !Int -- ^ The index to bind a free variable
               | BoundAtom
               | Bound !Int -- ^ The index to look for the binding of this variable
               deriving (Show)

data AdornedClause a = AdornedClause { adornedClauseRelation :: Relation
                                     , adornedClauseTerms :: [(Term a, Adornment)]
                                     }

instance (Show a) => Show (AdornedClause a) where
  show (AdornedClause p ats) =
    printf "%s(%s)" (show p) (intercalate ", " (map showAT ats))
    where
      showAT (t, a) = printf "%s[%s]" (show t) (show a)

-- | Body clauses can be normal clauses, negated clauses, or
-- conditionals.  Conditionals are arbitrary-arity (via a list)
-- functions over literals and logic variables.
data Literal ctype a = Literal (ctype a)
                     | NegatedLiteral (ctype a)
                     | ConditionalClause ([a] -> Bool) [Term a] (HashMap (Term a) Int)
--                     | MagicLiteral (ctype a)

lit :: Relation -> [Term a] -> Literal Clause a
lit p ts = Literal $ Clause p ts

negLit :: Relation -> [Term a] -> Literal Clause a
negLit p ts = NegatedLiteral $ Clause p ts

cond1 :: (Eq a, Hashable a)
         => (a -> Bool)
         -> Term a
         -> Literal Clause a
cond1 p t = ConditionalClause (\[x] -> p x) [t] mempty

cond2 :: (Eq a, Hashable a)
         => (a -> a -> Bool)
         -> (Term a, Term a)
         -> Literal Clause a
cond2 p (t1, t2) = ConditionalClause (\[x1, x2] -> p x1 x2) [t1, t2] mempty


cond3 :: (Eq a, Hashable a)
         => (a -> a -> a -> Bool)
         -> (Term a, Term a, Term a)
         -> Literal Clause a
cond3 p (t1, t2, t3) = ConditionalClause (\[x1, x2, x3] -> p x1 x2 x3) [t1, t2, t3] mempty

cond4 :: (Eq a, Hashable a)
         => (a -> a -> a -> a -> Bool)
         -> (Term a, Term a, Term a, Term a)
         -> Literal Clause a
cond4 p (t1, t2, t3, t4) = ConditionalClause (\[x1, x2, x3, x4] -> p x1 x2 x3 x4) [t1, t2, t3, t4] mempty

cond5 :: (Eq a, Hashable a)
         => (a -> a -> a -> a -> a -> Bool)
         -> (Term a, Term a, Term a, Term a, Term a)
         -> Literal Clause a
cond5 p (t1, t2, t3, t4, t5) = ConditionalClause (\[x1, x2, x3, x4, x5] -> p x1 x2 x3 x4 x5) [t1, t2, t3, t4, t5] mempty

instance (Show a, Show (ctype a)) => Show (Literal ctype a) where
  show (Literal c) = show c
  show (NegatedLiteral c) = '~' : show c
  show (ConditionalClause _ ts _) = printf "f(%s)" (show ts)

-- | A rule has a head and body clauses.  Body clauses can be normal
-- clauses, negated clauses, or conditionals.
data Rule a = Rule { ruleHead :: AdornedClause a
                   , ruleBody :: [Literal AdornedClause a]
                   , ruleVariableMap :: HashMap (Term a) Int
                   }

instance (Show a) => Show (Rule a) where
  show (Rule h b _) = printf "%s |- %s" (show h) (intercalate ", " (map show b))

newtype Query a = Query { unQuery :: Clause a }

infixr 0 |-

-- | Assert a rule
(|-), assertRule :: (Failure DatalogError m)
        => (Relation, [Term a]) -- ^ The rule head
        -> [Literal Clause a] -- ^ Body literals
        -> QueryBuilder m a ()
(|-) = assertRule
assertRule (p, ts) b = do
  let h = Clause p ts
  s <- get
  put s { queryRules = (h, b) : queryRules s }


-- FIXME: Unify these and require inferred relations to be declared in
-- the schema at db construction time.  That also gives an opportunity
-- to name the columns

-- | Retrieve a Relation handle from the IDB.  If the Relation does
-- not exist, an error will be raised.
relationPredicateFromName :: (Failure DatalogError m)
                             => Text -> QueryBuilder m a Relation
relationPredicateFromName name = do
  idb <- gets intensionalDatabase
  case Relation name `elem` databaseRelations idb of
    False -> lift $ failure (NoRelationError name)
    True -> return $! Relation name

-- | Create a new predicate that will be referenced by an EDB rule
inferencePredicate :: (Failure DatalogError m)
                      => Text -> QueryBuilder m a Relation
inferencePredicate = return . Relation

-- | Bindings are vectors of values.  Each variable in a rule is
-- assigned an index in the Bindings during the adornment process.
-- When evaluating a rule, if a free variable is encountered, all of
-- its possible values are entered at the index for that variable in a
-- Bindings vector.  When a bound variable is encountered, its current
-- value is looked up from the Bindings.  If that value does not match
-- the concrete tuple being examined, that tuple is rejected.
newtype Bindings s a = Bindings (STVector s a)

-- | A partial tuple records the atoms in a tuple (with their indices
-- in the tuple).  These are primarily used in database queries.
newtype PartialTuple a = PartialTuple [(Int, a)]

instance Show (PartialTuple a) where
  show (PartialTuple vs) = show $ map (show . fst) vs

-- | Convert a 'Query' into a 'PartialTuple' that can be used in a
-- 'select' of the IDB
queryToPartialTuple :: Query a -> PartialTuple a
queryToPartialTuple (Query c) =
  PartialTuple $! foldr takeAtom [] (zip [0..] ts)
  where
    ts = clauseTerms c
    takeAtom (ix, t) acc =
      case t of
        Atom a -> (ix, a) : acc
        _ -> acc

-- | For each term in the clause, take it as a literal if it is bound
-- or is an atom.  Otherwise, leave it as free (not mentioned in the
-- partial tuple).
buildPartialTuple :: AdornedClause a -> Bindings s a -> ST s (PartialTuple a)
buildPartialTuple c binds =
  PartialTuple . reverse <$> foldM (takeBoundOrAtom binds) [] indexedClauses
  where
    indexedClauses = zip [0..] (adornedClauseTerms c)
    takeBoundOrAtom (Bindings bs) acc (ix, ta) =
      case ta of
        (Atom a, BoundAtom) -> return $ (ix, a) : acc
        (_, Bound slot) -> do
          b <- V.read bs slot
          return $ (ix, b) : acc
        _ -> return acc

-- | Determine if a PartialTuple and a concrete Tuple from the
-- database match.  Walks the partial tuple (which is sorted by index)
-- and the current tuple in parallel and tries to avoid allocations as
-- much as possible.
tupleMatches :: (Eq a) => PartialTuple a -> Tuple a -> Bool
tupleMatches (PartialTuple pvs) (Tuple vs) =
  parallelTupleWalk 0 pvs vs

parallelTupleWalk :: (Eq a) => Int -> [(Int, a)] -> [a] -> Bool
parallelTupleWalk _ [] _ = True
parallelTupleWalk !ix cpvs@((pix, pv):prest) (v:rest)
  | ix /= pix = parallelTupleWalk (ix+1) cpvs rest
  | v == pv = parallelTupleWalk (ix+1) prest rest
  | otherwise = False
parallelTupleWalk _ _ [] = error "Tuple emptied before partial tuple"

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
select db p = scanSpace filter db p

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
joinLiteral _ bs (ConditionalClause p vs m) =
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
bindingsToTuple :: (Eq a, Hashable a)
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
        Nothing -> error "NonVariableInRuleHead"
        Just ix -> V.read bs ix

-- | Ensure that the relation named by the clause argument is in the
-- database.  Get the DBRelation.  Then fold over the Bindings,
-- constructing a tuple for each one (that is inserted into the
-- relation).  Then build a new database with that relation replaced
-- with the new one.
projectLiteral :: (Eq a, Hashable a)
                  => Database a
                  -> AdornedClause a
                  -> HashMap (Term a) Int
                  -> [Bindings s a]
                  -> ST s (Database a)
projectLiteral db c vmap bs = do
  let r = adornedClauseRelation c
      rel = ensureDatabaseRelation db r (length (adornedClauseTerms c))
  rel' <- foldM project rel bs
  return $ replaceRelation db rel'
  where
    project !r b = do
      t <- bindingsToTuple c vmap b
      return $ addTupleToRelation r t

literalClauseRelation :: Literal AdornedClause a -> Maybe Relation
literalClauseRelation bc =
  case bc of
    Literal c -> Just $ adornedClauseRelation c
    NegatedLiteral c -> Just $ adornedClauseRelation c
    _ -> Nothing

ruleRelations :: Rule a -> [Relation]
ruleRelations (Rule h bcs _) = adornedClauseRelation h : mapMaybe literalClauseRelation bcs

-- | Turn a Clause into a Query.  This is meant to be the last
-- statement in a QueryBuilder monad.
issueQuery :: (Failure DatalogError m) => Relation -> [Term a] -> QueryBuilder m a (Query a)
issueQuery r ts = return $ Query $ Clause r ts

-- If the query has a bound literal, that influences the rules it
-- corresponds to.  Other rules are not affected.  Those positions
-- bound in the query are bound in the associated rules.
--
-- Note: all variables in the head must appear in the body
adornRule :: (Failure DatalogError m, Eq a, Hashable a)
              => Query a -> (Clause a, [Literal Clause a]) -> m (Rule a)
adornRule q (hd, lits) = do
  (vmap, lits') <- mapAccumM adornLiteral mempty lits
  (allVars, Literal hd') <- adornLiteral vmap (Literal hd)
  let headVars = HS.fromList (clauseTerms hd)
  -- FIXME: This test isn't actually strict enough.  All head vars
  -- must appear in a non-negative literal
  case headVars `HS.difference` (HS.fromList (HM.keys allVars)) == mempty of
    True -> return $! Rule hd' lits' allVars
    False -> failure RangeRestrictionViolation

adornLiteral :: (Failure DatalogError m, Eq a, Hashable a)
                => HashMap (Term a) Int
                -> Literal Clause a
                -> m (HashMap (Term a) Int, Literal AdornedClause a)
adornLiteral boundVars l =
  case l of
    Literal c -> adornClause Literal c
    NegatedLiteral c -> adornClause NegatedLiteral c
    ConditionalClause f ts _ -> return (boundVars, ConditionalClause f ts boundVars)
  where
    adornClause constructor (Clause p ts) = do
      (bound', ts') <- mapAccumM adornTerm boundVars ts
      let c' = constructor $ AdornedClause p ts'
      return (bound', c')
    adornTerm bvs t =
      case t of
        -- Atoms are always bound
        Atom _ -> return (bvs, (t, BoundAtom))
        BindVar _ -> error "Bind variables are only allowed in queries"
        Anything ->
          let ix = HM.size bvs
              t' = FreshVar ix
          in return (HM.insert t' ix bvs, (t', Free ix))
        LogicVar _ ->
          -- The first occurrence is Free, while the rest are Bound
          case HM.lookup t bvs of
            Just ix -> return (bvs, (t, Bound ix))
            Nothing ->
              let ix = HM.size bvs
              in return (HM.insert t ix bvs, (t, Free ix))
        FreshVar _ -> error "Users cannot create FreshVars"

-- | Run the QueryBuilder action to build a query and initial rule
-- database
--
-- Rules are adorned (marking each variable as Free or Bound as they
-- appear) before being returned.
runQuery :: (Failure DatalogError m, Eq a, Hashable a)
            => QueryBuilder m a (Query a) -> Database a -> m (Query a, [Rule a])
runQuery qm idb = do
  (q, QueryState _ rs) <- runStateT qm (QueryState idb [])
  rs' <- mapM (adornRule q) rs
  return (q, rs')

-- | A worker to apply a single rule to the database (producing a new
-- database).
applyRule :: (Failure DatalogError m, Eq a, Hashable a)
             => Database a -> Rule a -> m (Database a)
applyRule db r = return $ runST $ do
  v0 <- V.new (HM.size m)
  bs <- foldM (joinLiteral db) [Bindings v0] b
  projectLiteral db h m bs
  where
    h = ruleHead r
    b = ruleBody r
    m = ruleVariableMap r

queryPredicate :: Query a -> Relation
queryPredicate = clauseRelation . unQuery

-- | Apply bindings to a query
bindQuery :: Query a -> [(Text, a)] -> Query a
bindQuery (Query (Clause r ts)) bs =
  Query $ Clause r $ foldr applyBinding [] ts
  where
    applyBinding t acc =
      case t of
        LogicVar _ -> t : acc
        BindVar name ->
          case lookup name bs of
            Nothing -> error ("No binding provided for BindVar " ++ show name)
            Just b -> Atom b : acc
        Anything -> t : acc
        Atom _ -> t : acc
        FreshVar _ -> error "Users cannot provide FreshVars"

-- Helpers missing from the standard libraries

{-# INLINE mapAccumM #-}
-- | Monadic mapAccumL
mapAccumM :: (Monad m, MonadPlus p) => (acc -> x -> m (acc, y)) -> acc -> [x] -> m (acc, p y)
mapAccumM _ z [] = return (z, mzero)
mapAccumM f z (x:xs) = do
  (z', y) <- f z x
  (z'', ys) <- mapAccumM f z' xs
  return (z'', return y `mplus` ys)

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