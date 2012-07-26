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
  PartialTuple(..),
  (|-),
  assertRule,
  relationPredicateFromName,
  inferencePredicate,
  ruleRelations,
  issueQuery,
  runQuery,
  queryToPartialTuple,
  queryPredicate,
  lit,
  negLit,
  cond1,
  cond2,
  cond3,
  cond4,
  cond5,
  bindQuery,
  partitionRules
  ) where

import Control.Failure
import Control.Monad.State.Strict
import Data.Function ( on )
import Data.Hashable
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import Data.List ( intercalate, groupBy, sortBy )
import Data.Maybe ( mapMaybe )
import Data.Monoid
import Data.Text ( Text )
import qualified Data.Text as T
import Text.Printf

import Database.Datalog.Relation
import Database.Datalog.Errors
import Database.Datalog.Database

-- import Debug.Trace
-- debug = flip trace

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
               deriving (Eq, Show)

data AdornedClause a = AdornedClause { adornedClauseRelation :: Relation
                                     , adornedClauseTerms :: [(Term a, Adornment)]
                                     }

instance (Eq a) => Eq (AdornedClause a) where
  (AdornedClause r1 cs1) == (AdornedClause r2 cs2) = r1 == r2 && cs1 == cs2

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

instance (Eq a, Eq (ctype a)) => Eq (Literal ctype a) where
  (Literal c1) == (Literal c2) = c1 == c2
  (NegatedLiteral c1) == (NegatedLiteral c2) = c1 == c2
  _ == _ = False

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
--
-- FIXME: Check to make sure that clause arities match their declared
-- schema.
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
    False -> lift $ failure (NoRelationError (Relation name))
    True -> return $! Relation name

-- | Create a new predicate that will be referenced by an EDB rule
inferencePredicate :: (Failure DatalogError m)
                      => Text -> QueryBuilder m a Relation
inferencePredicate = return . Relation

-- | A partial tuple records the atoms in a tuple (with their indices
-- in the tuple).  These are primarily used in database queries.
newtype PartialTuple a = PartialTuple [Maybe a]

instance (Show a) => Show (PartialTuple a) where
  show (PartialTuple vs) = show $ map show vs

-- | Convert a 'Query' into a 'PartialTuple' that can be used in a
-- 'select' of the IDB
queryToPartialTuple :: Query a -> PartialTuple a
queryToPartialTuple (Query c) =
  PartialTuple $! map takeAtom ts
  where
    ts = clauseTerms c
    takeAtom t =
      case t of
        Atom a -> Just a
        _ -> Nothing



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

-- | Group rules by their head relations.  This is needed to perform
-- semi-naive evaluation easily.
partitionRules :: [Rule a] -> [[Rule a]]
partitionRules = groupBy gcmp . sortBy scmp
  where
    scmp = compare `on` (adornedClauseRelation . ruleHead)
    gcmp = (==) `on` (adornedClauseRelation . ruleHead)

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
