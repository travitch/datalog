{-# LANGUAGE FlexibleContexts #-}
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

import Control.Failure
import Control.Monad.State.Strict
import Data.Hashable
import Data.HashSet ( HashSet )
import qualified Data.HashSet as HS
import Data.Maybe ( mapMaybe )
import Data.Monoid
import Data.Text ( Text )

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

data Adornment = Free | Bound

data AdornedClause a = AdornedClause { adornedClausePredicate :: Predicate
                                     , adornedClauseTerms :: [(Term a, Adornment)]
                                     }

-- | Body clauses can be normal clauses, negated clauses, or
-- conditionals.  Conditionals are arbitrary-arity (via a list)
-- functions over literals and logic variables.
data Literal ctype a = Literal (ctype a)
                     | NegatedLiteral (ctype a)
                     | ConditionalClause ([a] -> Bool) [Term a]

-- | A rule has a head and body clauses.  Body clauses can be normal
-- clauses, negated clauses, or conditionals.
data Rule a = Rule { ruleHead :: AdornedClause a
                   , ruleBody :: [Literal AdornedClause a]
                   }

newtype Query a = Query { unQuery :: AdornedClause a }

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
data Bindings a = Bindings

instance Monoid (Bindings a) where
  mempty = Bindings
  mconcat _ _ = Bindings

-- | A partial tuple records the atoms in a tuple (with their indices
-- in the tuple).
data PartialTuple a = PartialTuple [(Int, a)]

bindingAt :: Bindings a -> Int -> a
bindingAt = undefined

-- | For each term in the clause, take it as a literal if it is bound
-- or is an atom.  Otherwise, leave it as free (not mentioned in the
-- partial tuple).
buildPartialTuple :: AdornedClause a -> Bindings a -> PartialTuple a
buildPartialTuple c binds =
  PartialTuple $ foldr (takeBoundOrAtom binds) [] (zip [0..] (adornedClauseTerms c))
  where
    takeBoundOrAtom bs (ix, ta) acc =
      case ta of
        (Atom a, _) -> (ix, a) : acc
        (_, Bound) -> (ix, bindingAt ix) : acc
        _ -> acc

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


joinLiteralWith :: Database a
                   -> AdornedClause a
                   -> Bindings a
                   -> (Bindings a -> PartialTuple a -> [Bindings a])
                   -> Bindings a
joinLiteralsWith = undefined

joinLiteral :: Database a -> Literal AdornedClause a -> Bindings a -> Bindings a
joinLiteral db (Literal c) bs = undefined
joinLiteral db (NegatedLiteral c) bs = undefined
joinLiteral db (ConditionalClause p vs) bs = undefined

projectLiteral :: Database a -> Literal AdornedClause a -> Bindings a -> Database a
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
issueQuery = return . adornQuery

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
  case headVars `HS.difference` allVars == mempty of
    True -> return $! Rule hd' lits'
    False -> failure RangeRestrictionViolation

adornQuery :: Clause a -> Query a
adornQuery (Clause p ts) = Query $ AdornedClause p $ map adorn ts
  where
    adorn t@(LogicVar _) = (t, Free)
    -- BoundVars will become bound by the time this matters
    adorn t = (t, Bound)

adornLiteral :: (Failure DatalogError m, Eq a, Hashable a)
                => HashSet (Term a)
                -> Literal Clause a
                -> m (HashSet (Term a), Literal AdornedClause a)
adornLiteral boundVars lit =
  case lit of
    Literal c -> adornClause Literal c
    NegatedLiteral c -> adornClause NegatedLiteral c
    ConditionalClause f ts -> return (boundVars, ConditionalClause f ts)
  where
    adornClause constructor (Clause p ts) = do
      (bound', ts') <- mapAccumM adornTerm boundVars ts
      let c' = constructor $ AdornedClause p ts'
      return (bound', c')
    adornTerm bvs t =
      case t of
        -- Atoms are always bound
        Atom _ -> return (bvs, (t, Bound))
        BindVar _ -> error "Bind variables are only allowed in queries"
        LogicVar _ ->
          -- The first occurrence is Free, while the rest are Bound
          case HS.member t bvs of
            True -> return (bvs, (t, Bound))
            False -> return (HS.insert t bvs, (t, Free))

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

mapAccumM :: (Monad m, MonadPlus p) => (acc -> x -> m (acc, y)) -> acc -> [x] -> m (acc, p y)
mapAccumM _ z [] = return (z, mzero)
mapAccumM f z (x:xs) = do
  (z', y) <- f z x
  (z'', ys) <- mapAccumM f z' xs
  return (z'', return y `mplus` ys)
