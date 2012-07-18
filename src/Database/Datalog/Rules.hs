{-# LANGUAGE FlexibleContexts, BangPatterns #-}
-- | FIXME: Change the adornment/query building process such that
-- conditional clauses are always processed last.  This is necessary
-- so that all variables are bound.
--
-- FIXME: Add an assertion to say that ConditionalClauses cannot have
-- Free variables.
module Database.Datalog.Rules (
  Adornment(..),
  Term(..),
  Clause(..),
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
  rulePredicates,
  issueQuery,
  applyRule,
  runQuery,
  select,
  queryToPartialTuple,
  queryPredicate
  ) where

import Control.Applicative
import Control.Failure
import Control.Monad.State.Strict
import Control.Monad.ST.Strict
import qualified Data.Foldable as F
import Data.Hashable
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import Data.HashSet ( HashSet )
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

import Debug.Trace
debug = flip trace

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
            | Atom a
              -- ^ A user-provided literal from the domain a

instance (Show a) => Show (Term a) where
  show (LogicVar t) = T.unpack t
  show (BindVar t) = "??" ++ T.unpack t
  show (Atom a) = show a

instance (Hashable a) => Hashable (Term a) where
  hash (LogicVar t) = hash t `combine` 1
  hash (BindVar t) = hash t `combine` 2
  hash (Atom a) = hash a

instance (Eq a) => Eq (Term a) where
  (LogicVar t1) == (LogicVar t2) = t1 == t2
  (BindVar t1) == (BindVar t2) = t1 == t2
  (Atom a1) == (Atom a2) = a1 == a2
  _ == _ = False

data Clause a = Clause { clausePredicate :: Predicate
                       , clauseTerms :: [Term a]
                       }

instance (Show a) => Show (Clause a) where
  show (Clause p ts) =
    printf "%s(%s)" (show p) (intercalate ", " (map show ts))

data Adornment = Free !Int -- ^ The index to bind a free variable
               | BoundAtom
               | Bound !Int -- ^ The index to look for the binding of this variable
               deriving (Show)

data AdornedClause a = AdornedClause { adornedClausePredicate :: Predicate
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
                     -- | Condition1 (a -> Bool) (Term a) (HashMap (Term a) Int)
                     -- | Condition2 (a -> a -> Bool) (Term a, Term a) (HashMap (Term a) Int)
                     -- | Condition3 (a -> a -> a -> Bool) (Term a, Term a, Term a) (HashMap (Term a) Int)
                     -- | Condition4 (a -> a -> a -> a -> Bool) (Term a, Term a, Term a, Term a) (HashMap (Term a) Int)
                     -- | Condition5 (a -> a -> a -> a -> a -> Bool) ((Term a, Term a, Term a, Term a, Term a) (HashMap (Term a) Int)

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
(|-) :: (Failure DatalogError m) => Clause a -> [Literal Clause a] -> QueryBuilder m a ()
(|-) = assertRule

-- | Assert a rule
assertRule :: (Failure DatalogError m) => Clause a -> [Literal Clause a] -> QueryBuilder m a ()
assertRule h b = do
  s <- get
  put s { queryRules = (h, b) : queryRules s }

-- | Retrieve a Relation handle from the IDB.  If the Relation does
-- not exist, an error will be raised.
relationPredicateFromName :: (Failure DatalogError m)
                             => Text -> QueryBuilder m a Predicate
relationPredicateFromName name = do
  idb <- gets intensionalDatabase
  case RelationPredicate (Relation name) `elem` databasePredicates idb of
    False -> lift $ failure (NoRelationError name)
    True -> return $! (RelationPredicate (Relation name))

-- | Create a new predicate that will be referenced by an EDB rule
inferencePredicate :: (Failure DatalogError m)
                      => Text -> QueryBuilder m a Predicate
inferencePredicate = return . InferencePredicate

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
data PartialTuple a = PartialTuple [(Int, a)]

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
-- database match.
tupleMatches :: (Eq a) => PartialTuple a -> Tuple a -> Bool
tupleMatches (PartialTuple pvs) (Tuple vs) =
  all lookMatch (zip [0..] vs)
  where
    lookMatch (ix, v) =
      case lookup ix pvs of
        Nothing -> True -- Not bound, so anything matches
        Just v' -> v == v'

{-# INLINE scanSpace #-}
-- | The common worker for 'select' and 'matchAny'
scanSpace :: (Eq a, Hashable a)
             => ((Tuple a -> Bool) -> HashSet (Tuple a) -> b)
             -> Database a
             -> Predicate
             -> PartialTuple a
             -> b
scanSpace f db p pt = f (tupleMatches pt) space
  where
    -- FIXME: This is where we use the index, if available.  If not,
    -- we have to fall back to a table scan

    -- Note that the relation might not exist in the database here
    -- because this is the first time data is being inferred for the
    -- EDB.  In that case, just start with empty data and the project
    -- step will insert the table into the database for the next step.
    space = fromMaybe mempty (dataForPredicate db p)

-- | Return all of the tuples in the given relation that match the
-- given PartialTuple
select :: (Eq a, Hashable a) => Database a -> Predicate -> PartialTuple a -> [Tuple a]
select db p = HS.toList . scanSpace HS.filter db p

-- | Return true if any tuples in the given relation match the given
-- 'PartialTuple'
anyMatch :: (Eq a, Hashable a) => Database a -> Predicate -> PartialTuple a -> Bool
anyMatch = scanSpace F.any

{-# INLINE joinLiteralWith #-}
-- | The common worker for the non-conditional clause join functions.
joinLiteralWith :: AdornedClause a
                   -> [Bindings s a]
                   -> (Bindings s a -> PartialTuple a -> ST s [Bindings s a])
                   -> ST s [Bindings s a]
joinLiteralWith c bs f = do
  r <- concatMapM (apply c f) bs
  return r `debug` printf "> %d input bindings -> %d output bindings\n" (length bs) (length r)
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
normalJoin db c binds pt = mapM (projectTupleOntoLiteral c binds) (ts `debug` printf "Join adding %d tuples\n" (length ts))
  where
    ts = select db (adornedClausePredicate c) pt `debug` (" Attempting a select with pt: " ++ show pt)

-- | Retain the input binding if there are no matches in the database
-- for the input PartialTuple.  Otherwise reject it.
negatedJoin :: (Eq a, Hashable a) => Database a -> AdornedClause a -> Bindings s a
               -> PartialTuple a -> ST s [Bindings s a]
negatedJoin db c binds pt =
  case anyMatch db (adornedClausePredicate c) pt of
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
  let p = adornedClausePredicate c
      r = predicateToRelation p
      rel = ensureDatabaseRelation db r (length (adornedClauseTerms c))
  rel' <- foldM project rel bs
  return $ replaceRelation db rel'
  where
    project !r b = do
      t <- bindingsToTuple c vmap b
      return $ addTupleToRelation r t

literalClausePredicate :: Literal AdornedClause a -> Maybe Predicate
literalClausePredicate bc =
  case bc of
    Literal c -> Just $ adornedClausePredicate c
    NegatedLiteral c -> Just $ adornedClausePredicate c
    _ -> Nothing

rulePredicates :: Rule a -> [Predicate]
rulePredicates (Rule h bcs _) = adornedClausePredicate h : mapMaybe literalClausePredicate bcs

-- | Turn a Clause into a Query.  This is meant to be the last
-- statement in a QueryBuilder monad.
issueQuery :: (Failure DatalogError m) => Clause a -> QueryBuilder m a (Query a)
issueQuery = return . Query

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
adornLiteral boundVars lit =
  case lit of
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
        LogicVar _ ->
          -- The first occurrence is Free, while the rest are Bound
          case HM.lookup t bvs of
            Just ix -> return (bvs, (t, Bound ix))
            Nothing ->
              let ix = HM.size bvs
              in return (HM.insert t ix bvs, (t, Free ix))

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
  bs <- foldM (joinLiteral db) [Bindings v0] b `debug` printf "Applying %d clauses in the rule body\n" (length b)
  projectLiteral db h m bs
  where
    h = ruleHead r
    b = ruleBody r
    m = ruleVariableMap r

queryPredicate :: Query a -> Predicate
queryPredicate = clausePredicate . unQuery

-- Helpers missing from the standard libraries

{-# INLINE mapAccumM #-}
-- | Monadic mapAccumL
mapAccumM :: (Monad m, MonadPlus p) => (acc -> x -> m (acc, y)) -> acc -> [x] -> m (acc, p y)
mapAccumM _ z [] = return (z, mzero)
mapAccumM f z (x:xs) = do
  (z', y) <- f z x
  (z'', ys) <- mapAccumM f z' xs
  return (z'', return y `mplus` ys)

{-# INLINE concatMapM #-}
concatMapM :: (Monad m) => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = liftM concat (mapM f xs)