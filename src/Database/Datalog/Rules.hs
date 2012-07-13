{-# LANGUAGE FlexibleContexts #-}
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
  QueryMonad,
  (|-),
  assertRule,
  relationPredicateFromName,
  rulePredicates,
  issueQuery,
  applyRule,
  runQuery
  ) where

import Control.Applicative
import Control.Failure
import Control.Monad.State.Strict
import Control.Monad.ST.Strict
import Data.Hashable
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import Data.HashSet ( HashSet )
import qualified Data.HashSet as HS
import Data.Maybe ( mapMaybe )
import Data.Monoid
import Data.Text ( Text )
import Data.Vector.Mutable ( STVector )
import qualified Data.Vector.Mutable as V

import Database.Datalog.Errors
import Database.Datalog.Database

data QueryState a = QueryState { intensionalDatabase :: Database a
                               , queryRules :: [(Clause a, [Literal Clause a])]
                               }

-- | The Monad in which queries are constructed and rules are declared
type QueryMonad m a = StateT (QueryState a) m


data Term a = LogicVar !Text
              -- ^ A basic logic variable.  Equality is based on the
              -- variable name.
            | BindVar !Text
              -- ^ A special variable available in queries that can be
              -- bound at query execution time
            | Atom a
              -- ^ A user-provided literal from the domain a

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

data Adornment = Free !Int -- ^ The index to bind a free variable
               | BoundAtom
               | Bound !Int -- ^ The index to look for the binding of this variable

data AdornedClause a = AdornedClause { adornedClausePredicate :: Predicate
                                     , adornedClauseTerms :: [(Term a, Adornment)]
                                     }

-- | Body clauses can be normal clauses, negated clauses, or
-- conditionals.  Conditionals are arbitrary-arity (via a list)
-- functions over literals and logic variables.
data Literal ctype a = Literal (ctype a)
                     | NegatedLiteral (ctype a)
                     | ConditionalClause ([a] -> Bool) [Term a] (HashMap (Term a) Int)

-- | A rule has a head and body clauses.  Body clauses can be normal
-- clauses, negated clauses, or conditionals.
data Rule a = Rule { ruleHead :: AdornedClause a
                   , ruleBody :: [Literal AdornedClause a]
                   }

newtype Query a = Query { unQuery :: Clause a }

infixr 0 |-

-- | Assert a rule
(|-) :: (Failure DatalogError m) => Clause a -> [Literal Clause a] -> QueryMonad m a ()
(|-) = assertRule

assertRule :: (Failure DatalogError m) => Clause a -> [Literal Clause a] -> QueryMonad m a ()
assertRule h b = do
  s <- get
  put s { queryRules = (h, b) : queryRules s }

-- | Retrieve a Relation handle from the IDB.  If the Relation does
-- not exist, an error will be raised.
relationPredicateFromName :: (Failure DatalogError m)
                             => Text -> QueryMonad m a Predicate
relationPredicateFromName name = do
  idb <- gets intensionalDatabase
  case RelationPredicate (Relation name) `elem` databasePredicates idb of
    False -> lift $ failure (NoRelationError name)
    True -> return $! (RelationPredicate (Relation name))

inferencePredicate :: (Failure DatalogError m)
                      => Text -> QueryMonad m a Predicate
inferencePredicate = return . InferencePredicate

-- | Bindings are
data Bindings s a = Bindings (STVector s a)

-- | A partial tuple records the atoms in a tuple (with their indices
-- in the tuple).
data PartialTuple a = PartialTuple [(Int, a)]

bindingAt :: Bindings s a -> Int -> ST s a
bindingAt (Bindings v) = V.read v

-- | For each term in the clause, take it as a literal if it is bound
-- or is an atom.  Otherwise, leave it as free (not mentioned in the
-- partial tuple).
buildPartialTuple :: AdornedClause a -> Bindings s a -> ST s (PartialTuple a)
buildPartialTuple c binds =
  PartialTuple . reverse <$> foldM (takeBoundOrAtom binds) [] indexedClauses
  where
    indexedClauses = zip [0..] (adornedClauseTerms c)
    takeBoundOrAtom bs acc (ix, ta) =
      case ta of
        (Atom a, BoundAtom) -> return $ (ix, a) : acc
        (_, Bound slot) -> do
          b <- bindingAt bs slot
          return $ (ix, b) : acc
        _ -> return acc

tupleMatches :: PartialTuple a -> Tuple a -> Bool
tupleMatches = undefined

scanSpace :: ((Tuple a -> Bool) -> [Tuple a] -> b)
             -> Database a
             -> Predicate
             -> PartialTuple a
             -> b
scanSpace f db p pt = f (tupleMatches pt) space
  where
    -- This is where we use the index, if available.  If not, we have
    -- to fall back to a table scan
    space = undefined

select :: Database a -> Predicate -> PartialTuple a -> [Tuple a]
select = scanSpace filter

anyMatch :: Database a -> Predicate -> PartialTuple a -> Bool
anyMatch = scanSpace any

{-# INLINE joinLiteralWith #-}
joinLiteralWith :: AdornedClause a
                   -> [Bindings s a]
                   -> (Bindings s a -> PartialTuple a -> ST s [Bindings s a])
                   -> ST s [Bindings s a]
joinLiteralWith c bs f = concatMapM (apply c f) bs
  where
    apply cl fn b = do
      pt <- buildPartialTuple cl b
      fn b pt

joinLiteral :: (Eq a, Hashable a)
               => Database a
               -> Literal AdornedClause a
               -> [Bindings s a]
               -> ST s [Bindings s a]
joinLiteral db (Literal c) bs = joinLiteralWith c bs (normalJoin db c)
joinLiteral db (NegatedLiteral c) bs = joinLiteralWith c bs (negatedJoin db c)
joinLiteral db (ConditionalClause p vs m) bs =
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

normalJoin :: Database a -> AdornedClause a -> Bindings s a -> PartialTuple a -> ST s [Bindings s a]
normalJoin db c binds pt = mapM (projectTupleOntoLiteral c binds) ts
  where
    ts = select db (adornedClausePredicate c) pt

negatedJoin :: Database a -> AdornedClause a -> Bindings s a -> PartialTuple a -> ST s [Bindings s a]
negatedJoin db c binds pt =
  case anyMatch db (adornedClausePredicate c) pt of
    False -> return []
    True -> return [binds]

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

projectLiteral :: Database a -> Literal AdornedClause a -> [Bindings s a] -> ST s (Database a)
projectLiteral = undefined

literalClausePredicate :: Literal AdornedClause a -> Maybe Predicate
literalClausePredicate bc =
  case bc of
    Literal c -> Just $ adornedClausePredicate c
    NegatedLiteral c -> Just $ adornedClausePredicate c
    _ -> Nothing

rulePredicates :: Rule a -> [Predicate]
rulePredicates (Rule h bcs) = adornedClausePredicate h : mapMaybe literalClausePredicate bcs

issueQuery :: (Failure DatalogError m) => Clause a -> m (Query a)
issueQuery = return . Query

-- If the query has a bound literal, that influences the rules it
-- corresponds to.  Other rules are not affected.  Those positions
-- bound in the query are bound in the associated rules.
--
-- Note: all variables in the head must appear in the body
adornRule :: (Failure DatalogError m, Eq a, Hashable a)
              => Query a -> (Clause a, [Literal Clause a]) -> m (Rule a)
adornRule q (hd, lits) = do
  (vmap, Literal hd') <- adornLiteral mempty (Literal hd)
  (allVars, lits') <- mapAccumM adornLiteral vmap lits
  let headVars = HS.fromList (clauseTerms hd)
  -- FIXME: This test isn't actually strict enough.  All head vars
  -- must appear in a non-negative literal
  case headVars `HS.difference` (HS.fromList (HM.keys allVars)) == mempty of
    True -> return $! Rule hd' lits'
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

-- | Run the QueryMonad action to build a query and initial rule
-- database
--
-- Rules are adorned (marking each variable as Free or Bound as they
-- appear) before being returned.
runQuery :: (Failure DatalogError m, Eq a, Hashable a)
            => QueryMonad m a (Query a) -> Database a -> m (Query a, [Rule a])
runQuery qm idb = do
  (q, QueryState _ rs) <- runStateT qm (QueryState idb [])
  rs' <- mapM (adornRule q) rs
  return (q, rs')

applyRule :: (Failure DatalogError m) => Database a -> Rule a -> m (Database a)
applyRule db r = undefined

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