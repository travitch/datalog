{-# LANGUAGE BangPatterns #-}
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
  Query(..),
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

import qualified Control.Monad.Catch as E
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.State.Strict
import           Data.Function ( on )
import           Data.Hashable
import           Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import           Data.List ( intercalate, groupBy, sortBy )
import           Data.Maybe ( mapMaybe )
import           Data.Monoid
import           Data.Text ( Text )
import qualified Data.Text as T
import           Text.Printf ( printf )

import           Prelude

import           Database.Datalog.Adornment
import           Database.Datalog.Relation
import           Database.Datalog.Errors
import           Database.Datalog.Database

-- import Debug.Trace
-- debug = flip trace

data QueryState a = QueryState { intensionalDatabase :: Database a
                               , conditionalIdSource :: Int
                               , queryRules :: [(Clause a, [Literal Clause a])]
                               }

-- | The Monad in which queries are constructed and rules are declared
type QueryBuilder m a = StateT (QueryState a) m

nextConditionalId :: (E.MonadThrow m) => QueryBuilder m a Int
nextConditionalId = do
  s <- get
  let cid = conditionalIdSource s
  put s { conditionalIdSource = cid + 1 }
  return cid

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
  hashWithSalt s (LogicVar t) =
    s `hashWithSalt` t `hashWithSalt` (1 :: Int)
  hashWithSalt s (BindVar t) =
    s `hashWithSalt` t `hashWithSalt` (2 :: Int)
  hashWithSalt s (Atom a) = s `hashWithSalt` a
  hashWithSalt s Anything = s `hashWithSalt` (99 :: Int)
  hashWithSalt s (FreshVar i) =
    s `hashWithSalt` i `hashWithSalt` (22 :: Int)

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

instance (Eq a) => Eq (Clause a) where
  (Clause r1 ts1) == (Clause r2 ts2) = r1 == r2 && ts1 == ts2

instance (Show a) => Show (Clause a) where
  show (Clause p ts) =
    printf "%s(%s)" (show p) (intercalate ", " (map show ts))


data AdornedClause a = AdornedClause { adornedClauseRelation :: Relation
                                     , adornedClauseTerms :: [(Term a, Adornment)]
                                     }

instance (Eq a) => Eq (AdornedClause a) where
  (AdornedClause r1 cs1) == (AdornedClause r2 cs2) = r1 == r2 && cs1 == cs2

instance (Hashable a) => Hashable (AdornedClause a) where
  hashWithSalt s (AdornedClause r ts) =
    s `hashWithSalt` r `hashWithSalt` ts

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
                     | ConditionalClause Int ([a] -> Bool) [Term a] (HashMap (Term a) Int)

-- | This equality instance is complicated because conditional clauses
-- contain functions.  We assign a unique id at conditional clause
-- creation time so they have identity and we can compare on that.
-- Rules from different queries cannot be compared safely, but that
-- shouldn't be a problem because there isn't really a way to sneak a
-- rule reference out of a query.  If there is a shady way to do so,
-- don't because it will be bad.
instance (Eq a, Eq (ctype a)) => Eq (Literal ctype a) where
  (Literal c1) == (Literal c2) = c1 == c2
  (NegatedLiteral c1) == (NegatedLiteral c2) = c1 == c2
  (ConditionalClause cid1 _ _ _) == (ConditionalClause cid2 _ _ _) = cid1 == cid2
  _ == _ = False

instance (Hashable a, Hashable (ctype a)) => Hashable (Literal ctype a) where
  hashWithSalt s (Literal c) =
    s `hashWithSalt` c `hashWithSalt` (1 :: Int)
  hashWithSalt s (NegatedLiteral c) =
    s `hashWithSalt` c `hashWithSalt` (2 :: Int)
  hashWithSalt s (ConditionalClause cid _ ts vm) =
    s `hashWithSalt` cid `hashWithSalt` ts `hashWithSalt` HM.size vm

lit :: (E.MonadThrow m) => Relation -> [Term a] -> QueryBuilder m a (Literal Clause a)
lit p ts = return $ Literal $ Clause p ts

negLit :: (E.MonadThrow m) => Relation -> [Term a] -> QueryBuilder m a (Literal Clause a)
negLit p ts = return $ NegatedLiteral $ Clause p ts

cond1 :: (E.MonadThrow m, Eq a, Hashable a)
         => (a -> Bool)
         -> Term a
         -> QueryBuilder m a (Literal Clause a)
cond1 p t = do
  cid <- nextConditionalId
  return $ ConditionalClause cid (\[x] -> p x) [t] mempty

cond2 :: (E.MonadThrow m, Eq a, Hashable a)
         => (a -> a -> Bool)
         -> (Term a, Term a)
         -> QueryBuilder m a (Literal Clause a)
cond2 p (t1, t2) = do
  cid <- nextConditionalId
  return $ ConditionalClause cid (\[x1, x2] -> p x1 x2) [t1, t2] mempty


cond3 :: (E.MonadThrow m, Eq a, Hashable a)
         => (a -> a -> a -> Bool)
         -> (Term a, Term a, Term a)
         -> QueryBuilder m a (Literal Clause a)
cond3 p (t1, t2, t3) = do
  cid <- nextConditionalId
  return $ ConditionalClause cid (\[x1, x2, x3] -> p x1 x2 x3) [t1, t2, t3] mempty

cond4 :: (E.MonadThrow m, Eq a, Hashable a)
         => (a -> a -> a -> a -> Bool)
         -> (Term a, Term a, Term a, Term a)
         -> QueryBuilder m a (Literal Clause a)
cond4 p (t1, t2, t3, t4) = do
  cid <- nextConditionalId
  return $ ConditionalClause cid (\[x1, x2, x3, x4] -> p x1 x2 x3 x4) [t1, t2, t3, t4] mempty

cond5 :: (E.MonadThrow m, Eq a, Hashable a)
         => (a -> a -> a -> a -> a -> Bool)
         -> (Term a, Term a, Term a, Term a, Term a)
         -> QueryBuilder m a (Literal Clause a)
cond5 p (t1, t2, t3, t4, t5) = do
  cid <- nextConditionalId
  return $ ConditionalClause cid (\[x1, x2, x3, x4, x5] -> p x1 x2 x3 x4 x5) [t1, t2, t3, t4, t5] mempty

instance (Show a, Show (ctype a)) => Show (Literal ctype a) where
  show (Literal c) = show c
  show (NegatedLiteral c) = '~' : show c
  show (ConditionalClause _ _ ts _) = printf "f(%s)" (show ts)

-- | A rule has a head and body clauses.  Body clauses can be normal
-- clauses, negated clauses, or conditionals.
data Rule a = Rule { ruleHead :: AdornedClause a
                   , ruleBody :: [Literal AdornedClause a]
                   , ruleVariableMap :: HashMap (Term a) Int
                   }

instance (Show a) => Show (Rule a) where
  show (Rule h b _) = printf "%s |- %s" (show h) (intercalate ", " (map show b))

instance (Eq a) => Eq (Rule a) where
  (Rule h1 b1 vms1) == (Rule h2 b2 vms2) =
    h1 == h2 && b1 == b2 && vms1 == vms2

instance (Hashable a) => Hashable (Rule a) where
  hashWithSalt s (Rule h b vms) =
    s `hashWithSalt` h `hashWithSalt` b `hashWithSalt` HM.size vms

newtype Query a = Query { unQuery :: Clause a }
                deriving (Show)
infixr 0 |-

-- | Assert a rule
--
-- FIXME: Check to make sure that clause arities match their declared
-- schema.
(|-), assertRule :: (E.MonadThrow m)
        => (Relation, [Term a]) -- ^ The rule head
        -> [QueryBuilder m a (Literal Clause a)] -- ^ Body literals
        -> QueryBuilder m a ()
(|-) = assertRule
assertRule (p, ts) b = do
  -- FIXME: Assert that Anything does not appear in the head terms
  -- (that is a range restriction violation).  Also check the range
  -- restriction here.
  b' <- sequence b
  let h = Clause p ts
      b'' = fst $ foldr freshenVars ([], [0..]) b'
  s <- get
  put s { queryRules = (h, b'') : queryRules s }

-- | Replace all instances of Anything with a FreshVar with a unique
-- (to the rule) index.  This lets later evaluation stages ignore
-- these and just deal with clean FreshVars.
freshenVars :: Literal Clause a
               -> ([Literal Clause a], [Int])
               -> ([Literal Clause a], [Int])
freshenVars l (cs, ixSrc) =
  case l of
    ConditionalClause _ _ _ _ -> (l : cs, ixSrc)
    Literal (Clause h ts) ->
      let (ts', ixRest) = foldr freshen ([], ixSrc) ts
      in (Literal (Clause h ts') : cs, ixRest)
    NegatedLiteral (Clause h ts) ->
      let (ts', ixRest) = foldr freshen ([], ixSrc) ts
      in (NegatedLiteral (Clause h ts') : cs, ixRest)
  where
    freshen t (ts, src) =
      case t of
        Anything -> (FreshVar (head src) : ts, tail src)
        _ -> (t : ts, src)

-- FIXME: Unify these and require inferred relations to be declared in
-- the schema at db construction time.  That also gives an opportunity
-- to name the columns

-- | Retrieve a Relation handle from the IDB.  If the Relation does
-- not exist, an error will be raised.
relationPredicateFromName :: (E.MonadThrow m)
                             => Text
                             -> QueryBuilder m a Relation
relationPredicateFromName name = do
  let rel = Relation name
  idb <- gets intensionalDatabase
  case rel `elem` databaseRelations idb of
    False -> lift $ E.throwM (NoRelationError rel)
    True -> return rel

-- | Create a new predicate that will be referenced by an EDB rule
inferencePredicate :: (E.MonadThrow m)
                      => Text
                      -> QueryBuilder m a Relation
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
issueQuery :: (E.MonadThrow m) => Relation -> [Term a] -> QueryBuilder m a (Query a)
issueQuery r ts = return $ Query $ Clause r ts


-- | Run the QueryBuilder action to build a query and initial rule
-- database
--
-- Rules are adorned (marking each variable as Free or Bound as they
-- appear) before being returned.
runQuery :: (E.MonadThrow m, Eq a, Hashable a)
            => QueryBuilder m a (Query a) -> Database a -> m (Query a, [(Clause a, [Literal Clause a])])
runQuery qm idb = do
  (q, QueryState _ _ rs) <- runStateT qm (QueryState idb 0 [])
  return (q, rs)

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
