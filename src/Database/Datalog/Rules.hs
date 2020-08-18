{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
import qualified Data.Functor.Identity as DFI
import           Data.Kind ( Type )
import           Data.List ( groupBy, sortBy )
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some ( Some(..), mapSome )
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Text ( Text )
import qualified Data.Text as T
import           Data.Typeable ( Typeable )
import           Text.Printf ( printf )

import           Prelude

import           Database.Datalog.Adornment
import           Database.Datalog.Database
import           Database.Datalog.Errors
import qualified Database.Datalog.Panic as DDP
import           Database.Datalog.RelationSchema

-- import Debug.Trace
-- debug = flip trace

data QueryState (a :: k -> Type) (r :: k -> Type) =
  QueryState { intensionalDatabase :: Database a r
             , queryRules :: [QueryRule a r]
             }

-- | The Monad in which queries are constructed and rules are declared
newtype QueryBuilder m a r v =
  QueryBuilder { unQB :: CMS.StateT (QueryState a r) m v }
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
  QueryRule :: Clause a r tps -> Ctx.Assignment (Literal Clause a r) ctx -> QueryRule a r

-- | Terms that can appear in 'Clause's
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

data Clause a r tps where
  Clause :: RelationSchema r tps -> Ctx.Assignment (Term a) tps -> Clause a r tps

clauseTerms :: Clause a r tps -> Ctx.Assignment (Term a) tps
clauseTerms (Clause _schema terms) = terms

data AdornedClause a r tps where
  AdornedClause :: RelationSchema r tps -> Ctx.Assignment (Term a) tps -> Ctx.Assignment Adornment tps -> AdornedClause a r tps

adornedClauseSchema :: AdornedClause a r tps -> RelationSchema r tps
adornedClauseSchema (AdornedClause schema _terms _adornments) = schema

-- | Body clauses can be normal clauses, negated clauses, or
-- conditionals.  Conditionals are arbitrary-arity (via a list)
-- functions over literals and logic variables.
--
-- The @ctype@ parameter will be instantiated as either 'Clause' or 'AdornedClause'
data Literal clause a r tps where
  Literal :: clause a r tps -> Literal clause a r tps
  NegatedLiteral :: clause a r tps -> Literal clause a r tps
  ConditionalClause :: (Ctx.Assignment a tps -> Bool) -> Ctx.Assignment (Term a) tps -> Literal clause a r tps

lit :: RelationSchema r tps
    -> Ctx.Assignment (Term a) tps
    -> Literal Clause a r tps
lit p ts = Literal $ Clause p ts

negLit :: RelationSchema r tps
       -> Ctx.Assignment (Term a) tps
       -> Literal Clause a r tps
negLit p ts = NegatedLiteral $ Clause p ts

cond :: (Ctx.Assignment a tps -> Bool)
     -> Ctx.Assignment (Term a) tps
     -> Literal Clause a r tps
cond p ts = ConditionalClause p ts

-- | A rule has a head and body clauses.  Body clauses can be normal
-- clauses, negated clauses, or conditionals.
--
-- FIXME: Add the metadata mapping variables to term indexes
data Rule a r where
  Rule :: AdornedClause a r tps -> Ctx.Assignment (Literal AdornedClause a r) ctx -> Rule a r

ruleHead :: Rule a r -> Some (AdornedClause a r)
ruleHead (Rule hd _lits) = Some hd

ruleBody :: Rule a r -> Some (Ctx.Assignment (Literal AdornedClause a r))
ruleBody (Rule _hd lits) = Some lits

newtype Query a r tps = Query { unQuery :: Clause a r tps }
infixr 0 |-

-- | Assert a rule
(|-), assertRule :: (E.MonadThrow m)
                 => (RelationSchema r tps, Ctx.Assignment (Term a) tps)
                 -- ^ The rule head
                 -> Ctx.Assignment (Literal Clause a r) ctx
                 -- ^ Body literals
                 -> QueryBuilder m a r ()
(|-) = assertRule
assertRule (p, ts) b = do
  -- FIXME: Assert that Anything does not appear in the head terms
  -- (that is a range restriction violation).  Also check the range
  -- restriction here.
  let hd = Clause p ts
  let body = CMS.evalState (FC.traverseFC freshenVars b) 0
  let qr = QueryRule hd body
  CMS.modify' $ \qs -> qs { queryRules = qr : queryRules qs }

-- | Replace all occurrences of 'Anything' from the user's 'Rule' with a fresh
-- variable ('FreshVar') with a locally-unique label ('Int')
freshenVars :: Literal Clause a r tps -> CMS.State Int (Literal Clause a r tps)
freshenVars l =
  case l of
    Literal (Clause schema terms) -> do
      terms' <- FC.traverseFC freshen terms
      return (Literal (Clause schema terms'))
    NegatedLiteral (Clause schema terms) -> do
      terms' <- FC.traverseFC freshen terms
      return (NegatedLiteral (Clause schema terms'))
    ConditionalClause {} -> return l
  where
    freshen t =
      case t of
        Anything -> do
          label <- CMS.get
          CMS.modify' (+1)
          return (FreshVar label)
        _ -> return t

-- FIXME: Unify these and require inferred relations to be declared in
-- the schema at db construction time.  That also gives an opportunity
-- to name the columns

-- | Retrieve a Relation handle from the IDB.  If the Relation does
-- not exist, an error will be raised.
relationPredicateFromName :: forall k m (a :: k -> Type) r tps
                           . (E.MonadThrow m, PC.OrdF r, Typeable r, Typeable k)
                          => Ctx.Assignment r tps
                          -> Text
                          -> QueryBuilder m a r (RelationSchema r tps)
relationPredicateFromName reprs name = do
  let rel = RelationSchema reprs name
  idb <- CMS.gets intensionalDatabase
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

-- | Convert a 'Query' into a 'PartialTuple' that can be used in a
-- 'select' of the IDB
queryToPartialTuple :: forall a r tps . Query a r tps -> PartialTuple a tps
queryToPartialTuple (Query c) =
  PartialTuple $! Ctx.forIndex (Ctx.size ts) takeAtom MapF.empty
  where
    ts = clauseTerms c
    takeAtom :: forall tp . MapF.MapF (Ctx.Index tps) a -> Ctx.Index tps tp -> MapF.MapF (Ctx.Index tps) a
    takeAtom m idx =
      case ts Ctx.! idx of
        Atom a -> MapF.insert idx a m
        LogicVar {} -> m
        BindVar {} -> m
        FreshVar {} -> m
        Anything -> m

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
  (q, QueryState _ rs) <- CMS.runStateT (unQB qm) (QueryState idb [])
  return (q, rs)

-- | Group rules by their head relations.  This is needed to perform
-- semi-naive evaluation easily.
partitionRules :: (PC.OrdF r) => [Rule a r] -> [[Rule a r]]
partitionRules = groupBy gcmp . sortBy scmp
  where
    scmp = compare `on` (mapSome adornedClauseSchema . ruleHead)
    gcmp = (==) `on` (mapSome adornedClauseSchema . ruleHead)

queryPredicate :: Query a r tps -> RelationSchema r tps
queryPredicate (Query (Clause schema _terms)) = schema

-- | Apply bindings to a query
bindQuery :: forall a r tps
           . Query a r tps
          -> MapF.MapF (Ctx.Index tps) a
          -> Query a r tps
bindQuery (Query (Clause schema terms)) bindings =
  Query (Clause schema (DFI.runIdentity (Ctx.traverseWithIndex bindVariable terms)))
  where
    bindVariable :: forall tp . Ctx.Index tps tp -> Term a tp -> DFI.Identity (Term a tp)
    bindVariable idx t =
      case t of
        LogicVar {} -> return t
        Anything -> return t
        Atom {} -> return t
        BindVar _name ->
          case MapF.lookup idx bindings of
            Nothing -> return t
            Just val -> return (Atom val)
        FreshVar {} -> DDP.panic DDP.DatalogCore "bindQuery" ["FreshVar should not be exported to users"]
