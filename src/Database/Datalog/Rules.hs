{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeInType #-}
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
  cond,
  bindQuery,
  partitionRules
  ) where

import qualified Control.Monad.Catch as E
import qualified Control.Monad.State.Strict as CMS
import           Data.Function ( on )
import           Data.Hashable
import           Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import           Data.Kind ( Type )
import           Data.List ( intercalate, groupBy, sortBy )
import           Data.Maybe ( mapMaybe )
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some ( Some(..) )
import           Data.Text ( Text )
import qualified Data.Text as T
import           Text.Printf ( printf )

import           Prelude

import           Database.Datalog.Adornment
import           Database.Datalog.RelationSchema
import           Database.Datalog.Errors
import           Database.Datalog.Database

-- import Debug.Trace
-- debug = flip trace

data QueryState (a :: k -> Type) (r :: k -> Type) =
  QueryState { intensionalDatabase :: Database a r
             , queryRules :: [QueryRule a r]
             }

-- | The Monad in which queries are constructed and rules are declared
newtype QueryBuilder m a r v = QueryBuilder { unQB :: CMS.StateT (QueryState a r) m v }
  deriving ( Functor
           , Applicative
           , Monad
           , CMS.MonadState (QueryState a r)
           , E.MonadThrow
           )

data Binder tp where
  Binder :: T.Text -> Binder tp

-- | Rules provided by the user
--
-- This is the initial form of a rule before it has been analyzed and compiled
-- into and 'AdornedRule' with a binding pattern
data QueryRule a r where
  QueryRule :: RelationSchema r tps -> Ctx.Assignment Binder tps -> Ctx.Assignment (Literal Clause a r) ctx -> QueryRule a r

data Term a tp where
  -- | A user-provided ground term from the domain @a@
  Atom :: a tp -> Term a tp
  -- | A basic logic variable.  Equality is based on the variable name.
  LogicVar :: !T.Text -> Term a tp
  -- | A special variable available in queries that can be bound at query execution time
  BindVar :: !T.Text -> Term a tp
  -- | A fresh logic variable, generated internally for each Anything occurrence.  Not exposed to the user
  FreshVar :: !Int -> Term a tp
  -- | A term that is allowed to take any value (this is sugar for a fresh logic variable)
  Anything :: Term a tp


-- instance (Show a) => Show (Term a) where
--   show (LogicVar t) = T.unpack t
--   show (BindVar t) = "??" ++ T.unpack t
--   show (Atom a) = show a
--   show Anything = "*"
--   show (FreshVar _) = "*"

-- instance (Hashable a) => Hashable (Term a) where
--   hashWithSalt s (LogicVar t) =
--     s `hashWithSalt` t `hashWithSalt` (1 :: Int)
--   hashWithSalt s (BindVar t) =
--     s `hashWithSalt` t `hashWithSalt` (2 :: Int)
--   hashWithSalt s (Atom a) = s `hashWithSalt` a
--   hashWithSalt s Anything = s `hashWithSalt` (99 :: Int)
--   hashWithSalt s (FreshVar i) =
--     s `hashWithSalt` i `hashWithSalt` (22 :: Int)

-- instance (Eq a) => Eq (Term a) where
--   (LogicVar t1) == (LogicVar t2) = t1 == t2
--   (BindVar t1) == (BindVar t2) = t1 == t2
--   (Atom a1) == (Atom a2) = a1 == a2
--   Anything == Anything = True
--   FreshVar i1 == FreshVar i2 = i1 == i2
--   _ == _ = False

data Clause a r tps where
  Clause :: RelationSchema r tps -> Ctx.Assignment (Term a) tps -> Clause a r tps

data AdornedClause a r tps where
  AdornedClause :: RelationSchema r tps -> Ctx.Assignment (Term a) tps -> Ctx.Assignment Adornment tps -> AdornedClause a r tps

-- data Clause r a tps =
--   Clause { clauseRelation :: RelationSchema r tps
--          , clauseTerms :: Ctx.Assignment (Term a) tps
--          }

-- instance (Eq a) => Eq (Clause a) where
--   (Clause r1 ts1) == (Clause r2 ts2) = r1 == r2 && ts1 == ts2

-- instance (Show a) => Show (Clause a) where
--   show (Clause p ts) =
--     printf "%s(%s)" (show p) (intercalate ", " (map show ts))


-- data AdornedClause r a tps =
--   AdornedClause { adornedClauseRelation :: RelationSchema r tps
--                 , adornedClauseTerms :: Ctx.Assignment (Term a) tps
--                 , adornments :: Ctx.Assignment Adornment tps
--                 }

-- instance (Eq a) => Eq (AdornedClause a) where
--   (AdornedClause r1 cs1) == (AdornedClause r2 cs2) = r1 == r2 && cs1 == cs2

-- instance (Hashable a) => Hashable (AdornedClause a) where
--   hashWithSalt s (AdornedClause r ts) =
--     s `hashWithSalt` r `hashWithSalt` ts

-- instance (Show a) => Show (AdornedClause a) where
--   show (AdornedClause p ats) =
--     printf "%s(%s)" (show p) (intercalate ", " (map showAT ats))
--     where
--       showAT (t, a) = printf "%s[%s]" (show t) (show a)

-- | Body clauses can be normal clauses, negated clauses, or
-- conditionals.  Conditionals are arbitrary-arity (via a list)
-- functions over literals and logic variables.
--
-- The @ctype@ parameter will be instantiated as either 'Clause' or 'AdornedClause'
data Literal clause a r tps where
  Literal :: clause a r tps -> Literal clause a r tps
  NegatedLiteral :: clause a r tps -> Literal clause a r tps
  ConditionalClause :: Int -> (Ctx.Assignment a tps -> Bool) -> Ctx.Assignment (Term a) tps -> Literal clause a r tps

-- data Literal ctype a tp = Literal (ctype a tp)
--                      | NegatedLiteral (ctype a tp)
--                      | forall tps . ConditionalClause Int (Ctx.Assignment a tps -> Bool) (Ctx.Assignment (Term a) tps) (HashMap (Some (Term a)) Int)

-- | This equality instance is complicated because conditional clauses
-- contain functions.  We assign a unique id at conditional clause
-- creation time so they have identity and we can compare on that.
-- Rules from different queries cannot be compared safely, but that
-- shouldn't be a problem because there isn't really a way to sneak a
-- rule reference out of a query.  If there is a shady way to do so,
-- don't because it will be bad.
{-
instance (Eq (a tp), Eq (ctype a tp)) => Eq (Literal ctype a tp) where
  (Literal c1) == (Literal c2) = c1 == c2
  (NegatedLiteral c1) == (NegatedLiteral c2) = c1 == c2
  (ConditionalClause cid1 _ _ _) == (ConditionalClause cid2 _ _ _) = cid1 == cid2
  _ == _ = False

instance (Hashable (a tp), Hashable (ctype a tp)) => Hashable (Literal ctype a tp) where
  hashWithSalt s (Literal c) =
    s `hashWithSalt` c `hashWithSalt` (1 :: Int)
  hashWithSalt s (NegatedLiteral c) =
    s `hashWithSalt` c `hashWithSalt` (2 :: Int)
  hashWithSalt s (ConditionalClause cid _ ts vm) =
    s `hashWithSalt` cid `hashWithSalt` ts `hashWithSalt` HM.size vm
-}

lit :: RelationSchema r tps
    -> Ctx.Assignment (Term a) tps
    -> Literal Clause a r tps
lit p ts = Literal $ Clause p ts

negLit :: RelationSchema r tps
       -> Ctx.Assignment (Term a) tps
       -> Literal Clause a r tps
negLit p ts = NegatedLiteral $ Clause p ts

cond :: RelationSchema r tps
     -> (Ctx.Assignment a tps -> Bool)
     -> Ctx.Assignment (Term a) tps
     -> Literal Clause a r tps
cond _ p ts = ConditionalClause cid p ts

-- cond1 :: (E.MonadThrow m, Eq a, Hashable a)
--          => (a -> Bool)
--          -> Term a
--          -> QueryBuilder m a (Literal Clause a)
-- cond1 p t = do
--   cid <- nextConditionalId
--   return $ ConditionalClause cid (\[x] -> p x) [t] mempty

-- cond2 :: (E.MonadThrow m, Eq a, Hashable a)
--          => (a -> a -> Bool)
--          -> (Term a, Term a)
--          -> QueryBuilder m a (Literal Clause a)
-- cond2 p (t1, t2) = do
--   cid <- nextConditionalId
--   return $ ConditionalClause cid (\[x1, x2] -> p x1 x2) [t1, t2] mempty


-- cond3 :: (E.MonadThrow m, Eq a, Hashable a)
--          => (a -> a -> a -> Bool)
--          -> (Term a, Term a, Term a)
--          -> QueryBuilder m a (Literal Clause a)
-- cond3 p (t1, t2, t3) = do
--   cid <- nextConditionalId
--   return $ ConditionalClause cid (\[x1, x2, x3] -> p x1 x2 x3) [t1, t2, t3] mempty

-- cond4 :: (E.MonadThrow m, Eq a, Hashable a)
--          => (a -> a -> a -> a -> Bool)
--          -> (Term a, Term a, Term a, Term a)
--          -> QueryBuilder m a (Literal Clause a)
-- cond4 p (t1, t2, t3, t4) = do
--   cid <- nextConditionalId
--   return $ ConditionalClause cid (\[x1, x2, x3, x4] -> p x1 x2 x3 x4) [t1, t2, t3, t4] mempty

-- cond5 :: (E.MonadThrow m, Eq a, Hashable a)
--          => (a -> a -> a -> a -> a -> Bool)
--          -> (Term a, Term a, Term a, Term a, Term a)
--          -> QueryBuilder m a (Literal Clause a)
-- cond5 p (t1, t2, t3, t4, t5) = do
--   cid <- nextConditionalId
--   return $ ConditionalClause cid (\[x1, x2, x3, x4, x5] -> p x1 x2 x3 x4 x5) [t1, t2, t3, t4, t5] mempty

-- instance (Show (a tp), Show (ctype a tp)) => Show (Literal ctype a tp) where
--   show (Literal c) = show c
--   show (NegatedLiteral c) = '~' : show c
--   show (ConditionalClause _ _ ts _) = printf "f(%s)" (show ts)

-- | A rule has a head and body clauses.  Body clauses can be normal
-- clauses, negated clauses, or conditionals.
--
-- FIXME: Add the metadata mapping variables to term indexes
data Rule a r where
  Rule :: AdornedClause a r tps -> Ctx.Assignment (Literal AdornedClause a r) ctx -> Rule a r
                   -- , ruleVariableMap :: HashMap (Term a) Int
                   -- }



-- instance (Show a) => Show (Rule a) where
--   show (Rule h b _) = printf "%s |- %s" (show h) (intercalate ", " (map show b))

-- instance (Eq a) => Eq (Rule a) where
--   (Rule h1 b1 vms1) == (Rule h2 b2 vms2) =
--     h1 == h2 && b1 == b2 && vms1 == vms2

-- instance (Hashable a) => Hashable (Rule a) where
--   hashWithSalt s (Rule h b vms) =
--     s `hashWithSalt` h `hashWithSalt` b `hashWithSalt` HM.size vms

newtype Query a r tps = Query { unQuery :: Clause a r tps }
                      -- deriving (Show)
infixr 0 |-

-- | Assert a rule
--
-- FIXME: Check to make sure that clause arities match their declared
-- schema.
(|-), assertRule :: (E.MonadThrow m)
        => (RelationSchema r tps, Ctx.Assignment (Term a) tps) -- ^ The rule head
        -> Ctx.Assignment (Literal Clause a r) ctx -- ^ Body literals
        -> QueryBuilder m a r ()
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
--
-- FIXME: the freshening might be better in terms of the Ctx.Index type
freshenVars :: Literal Clause a r tps
            -> ([Literal Clause a r tps], [Int])
            -> ([Literal Clause a r tps], [Int])
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
relationPredicateFromName :: (E.MonadThrow m, PC.OrdF r)
                          => Ctx.Assignment r tps
                          -> Text
                          -> QueryBuilder m a r (RelationSchema r tps)
relationPredicateFromName reprs name = do
  let rel = RelationSchema reprs name
  idb <- gets intensionalDatabase
  case lookupRelation rel idb of
    Nothing -> E.throwM (NoRelationError rel)
    Just _r -> return rel

-- | Create a new predicate that will be referenced by an EDB rule
inferencePredicate :: (E.MonadThrow m)
                      => Ctx.Assignment r tps
                      -> T.Text
                      -> QueryBuilder m a r (RelationSchema r tps)
inferencePredicate reprs name = return (RelationSchema reprs name)

-- | A partial tuple records the atoms in a tuple (with their indices
-- in the tuple).  These are primarily used in database queries.
newtype PartialTuple a tps = PartialTuple (MapF.MapF (Ctx.Index tps) a) --[Maybe a]

-- instance (Show a) => Show (PartialTuple a) where
--   show (PartialTuple vs) = show $ map show vs

-- | Convert a 'Query' into a 'PartialTuple' that can be used in a
-- 'select' of the IDB
queryToPartialTuple :: Query a r tps -> PartialTuple a tps
queryToPartialTuple (Query c) =
  PartialTuple $! map takeAtom ts
  where
    ts = clauseTerms c
    takeAtom t =
      case t of
        Atom a -> Just a
        _ -> Nothing



literalClauseRelation :: Literal AdornedClause a r tps -> Maybe (RelationSchema r tps)
literalClauseRelation bc =
  case bc of
    Literal c -> Just $ adornedClauseRelation c
    NegatedLiteral c -> Just $ adornedClauseRelation c
    _ -> Nothing

ruleRelations :: Rule a r -> [Some (RelationSchema r)]
ruleRelations (Rule h bcs _) = adornedClauseRelation h : mapMaybe literalClauseRelation bcs

-- | Turn a Clause into a Query.  This is meant to be the last
-- statement in a QueryBuilder monad.
issueQuery :: (E.MonadThrow m) => RelationSchema r tps -> Ctx.Assignment (Term a) tps -> QueryBuilder m a r (Query a r tps)
issueQuery r ts = return $ Query $ Clause r ts


-- | Run the QueryBuilder action to build a query and initial rule
-- database
--
-- Rules are adorned (marking each variable as Free or Bound as they
-- appear) before being returned.
runQuery :: (E.MonadThrow m)
         => QueryBuilder m a r (Query a r tps)
         -> Database a r
         -> m (Query a r tps, [QueryRule a r])
runQuery qm idb = do
  (q, QueryState _ rs) <- runStateT qm (QueryState idb [])
  return (q, rs)

-- | Group rules by their head relations.  This is needed to perform
-- semi-naive evaluation easily.
partitionRules :: [Rule a r] -> [[Rule a r]]
partitionRules = groupBy gcmp . sortBy scmp
  where
    scmp = compare `on` (adornedClauseRelation . ruleHead)
    gcmp = (==) `on` (adornedClauseRelation . ruleHead)

queryPredicate :: Query a r tps -> RelationSchema r tps
queryPredicate (Query (Clause schema _terms)) = schema

data QueryBinding a tp where
  QueryBinding :: T.Text -> a tp -> QueryBinding a tp

-- | Apply bindings to a query
bindQuery :: Query a r tps -> [Some (QueryBinding a)] -> Query a r tps
bindQuery = undefined

-- bindQuery (Query (Clause r ts)) bs =
--   Query $ Clause r $ foldr applyBinding [] ts
--   where
--     applyBinding t acc =
--       case t of
--         LogicVar _ -> t : acc
--         BindVar name ->
--           case lookup name bs of
--             Nothing -> error ("No binding provided for BindVar " ++ show name)
--             Just b -> Atom b : acc
--         Anything -> t : acc
--         Atom _ -> t : acc
--         FreshVar _ -> error "Users cannot provide FreshVars"
