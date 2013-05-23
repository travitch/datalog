{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Database.Datalog.REPL.Datalog
  (
    DB(..)
  , mkDb
  , ValueInfo(..)
  ) where


import Data.Hashable
import Control.Monad.State
import Data.Map (Map)
import Data.Maybe
import Data.Text hiding (map,concatMap)
import Database.Datalog.REPL.Backend
import Database.Datalog.REPL.Parser
import qualified Data.List as L
import qualified Data.Map as Map
import qualified Data.Text as T
import qualified Database.Datalog as D

-- ---------------------------------------------------------------------

-- |Base types that can be stored in the database
data ValueInfo = VV !Text -- ^Value
                   deriving (Eq,Ord,Show)

instance Hashable ValueInfo where
  hashWithSalt s (VV r)  = s `hashWithSalt` r `hashWithSalt` (3 :: Int)

-- ---------------------------------------------------------------------

data DB = DB { fullyExtended :: Bool, db :: Datalog }


combine :: Datalog -> Datalog -> Datalog
-- combine a b = g (mappend a b) where
--  g (x, y) = (L.nub x, L.nub y)
combine (DL fa ra qra) (DL fb rb qrb) = (DL f r qr)
  where
    f = Map.unionWith combineOp fa fb
    r = Map.unionWith combineOp ra rb

    combineOp as bs = L.nub (as++bs)
    qr = L.nub (qra++qrb)

-- return all derived facts, but don't commit them
derive :: State DB DB
derive = do
  DB b adb <- get
  return $ if b then DB b adb
                -- else DB True (combine db ((uncurry seminaive db, [])))
                else DB True adb

instance Backend (State DB) where
   -- facts = liftM (fst . db) derive
   facts   = liftM (L.concat . Map.elems . dlFacts . db) derive
   rules   = liftM (L.concat . Map.elems . dlRules . db) derive
   queries = liftM (                     dlQueries . db) derive

   memoAll = derive >>= put
   declare adb = modify (\(DB _ db0) -> DB False (combine db0 adb))

   -- query :: Atom Term -> f (Maybe Subst)
   -- query :: Atom Term -> f ([Fact]
   query q = do 
     DB _b adb <- get
     let r= (executeQuery q adb) :: Maybe [Fact]
     let res = fromMaybe [] r
     -- TODO: currently replacing old query results, perhaps keep them?
     put (DB False (adb { dlQueries = [(q,res)] }))
     return res

   fullDb = do 
      d <- get
      return (db d)

-- ---------------------------------------------------------------------

executeQuery :: (D.Failure D.DatalogError m)
   => Atom Term -> Datalog -> m ([Fact])
executeQuery q (DL factMap ruleMap _qr) = do
  let
     edb = mkDb factMap
     dq  = mkQuery ruleMap q
  r <- D.queryDatabase edb dq
  -- TODO: identify the original Con Id value
  --       will have to post-process, it is not available in this environment
  -- let res = map (\[VV var,VV val] -> (V $ T.unpack var,C (-1) (T.unpack val)) ) r

  let res = map oneFact r
      oneFact bs = Atom (atomPred q) vars
        where vars = map (\(VV v) -> C (-1) (T.unpack v)) bs

  return res

{-

Generate a database from the facts:

*Database.Datalog.REPL.Parser> run "a(b,c)."
Right ([Atom (C 0 "a") [C 1 "b",C 2 "c"]],[])

And rules:

*Database.Datalog.REPL.Parser> run "c(B,C) :- c(A,B),c(A,C)."
Right ([],[Rule (Atom (C 0 "c") [Var (V "B"),Var (V "C")]) [Pat (Atom (C 0 "c") [Var (V "A"),Var (V "B")]),Pat (Atom (C 0 "c") [Var (V "A"),Var (V "C")])]])
*Database.Datalog.REPL.Parser> 


A Datalog database, organised by name/arity
(fromList 
[
("a:2",[Atom (C 1 "a") [C 2 "b",C 3 "c"]]),
("a:3",[Atom (C 1 "a") [C 2 "b",C 3 "c",C 6 "d"]]),
("x:2",[Atom (C 0 "x") [C 4 "y",C 5 "z"]])
],

fromList 
[
("x:2",
  [
  Rule (Atom (C 0 "x") [Var (V "A"),Var (V "B")]) [Pat (Atom (C 1 "a") [Var (V "A"),Var (V "B")])],
  Rule (Atom (C 0 "x") [Var (V "Y"),Var (V "Z")]) [Pat (Atom (C 0 "x") [Var (V "Y"),Var (V "X")]),Pat (Atom (C 0 "x") [Var (V "X"),Var (V "Z")])]])
]
)

-}

-- ---------------------------------------------------------------------

relationName :: (String,Int) -> T.Text
relationName (name,arity) = T.pack (name ++ ":" ++ (show arity))

-- ---------------------------------------------------------------------

mkDb :: Map.Map AtomSelector [Fact] -> D.Database ValueInfo
mkDb factMap = fromJust mkDb
  where
    mkDb = D.makeDatabase $ do
      mapM_  makeRelation $ Map.toList factMap

makeRelation ((name,arity),facts) = do
  rel <- D.addRelation (relationName (name,arity)) arity
  mapM_ (D.assertFact rel) (map toFact facts)

toFact :: Fact -> [ValueInfo]
toFact f = map (\p -> VV $ T.pack $ conName p) (atomArgs f)

-- ---------------------------------------------------------------------

mkQuery :: (D.Failure D.DatalogError m )
  => Map.Map AtomSelector [Rule] -> Atom Term 
  -> D.QueryBuilder m ValueInfo (D.Query ValueInfo)
mkQuery ruleMap q = do

 mapM_ makeQueryRelation $ Map.toList ruleMap

 qrel <- toRel q
 D.issueQuery qrel (headVars q)
 -- D.issueQuery qrel [D.Atom (VV "b"),D.LogicVar "X"]

{-
      parentOf <- relationPredicateFromName "parentOf"
      ancestorOf <- inferencePredicate "ancestorOf"
      let x = LogicVar "x"
          y = LogicVar "y"
          z = LogicVar "z"
      (ancestorOf, [x, y]) |- [ lit parentOf [x, y] ]
      (ancestorOf, [x, y]) |- [ lit parentOf [x, z], lit ancestorOf [z, y] ]
      issueQuery ancestorOf [x, Atom "John" ]

-}

makeQueryRelation :: D.Failure D.DatalogError m =>
   ((String,Int),[Rule]) -> D.QueryBuilder m ValueInfo (D.Relation)
makeQueryRelation ((name,arity),rules) = do
  rel <- D.inferencePredicate (relationName (name,arity))
  let varNames = map (T.pack . varName)  $ varsInRules rules
  let vars = Map.fromList $ map (\n -> (n,D.LogicVar n)) varNames

  mapM_ (\rule -> queryClause rel rule vars) rules

  return rel

-- ---------------------------------------------------------------------

toRel :: D.Failure D.DatalogError m
  => Atom t -> D.QueryBuilder m a D.Relation
toRel x = D.inferencePredicate (relationName ((atomName x),arity))
    where arity = L.length $ atomArgs x

headVars :: Atom Term -> [D.Term ValueInfo]
headVars h = map toDTerm $ atomArgs h 

toDTerm :: Term -> D.Term ValueInfo
-- Must be either D.LogicVar or D.Atom
toDTerm (Var n) = D.LogicVar (T.pack $ varName n)
toDTerm (Con n) = D.Atom (VV (T.pack $ conName n))


-- ---------------------------------------------------------------------

queryClause ::
  D.Failure D.DatalogError m =>
  D.Relation -> Rule -> Map Text (D.Term ValueInfo) -> D.QueryBuilder m ValueInfo ()
queryClause rel rule vars = do
  let (Rule head body) = rule

  let bodyTerms = map toDClause body

      toDClause (Pat term) = do
        rel <- toRel term
        let clauses = map toDTerm $ atomArgs term
        D.lit    rel clauses
      toDClause (Not term) = do
        rel <- toRel term
        let clauses = map toDTerm $ atomArgs term
        D.negLit rel clauses

  (rel, headVars head) D.|- bodyTerms

-- ---------------------------------------------------------------------

varsInRules :: [Rule] -> [Var]
varsInRules rules = L.nub $ go [] rules
  where
    go vs [] = vs
    go vs (r:rs) = go ((varsForRule r) ++ vs) rs
    
    varsForRule (Rule _ terms) = map (\(Var v) -> v) 
                                 $ L.filter isVar $ concatMap atomArgs 
                                       $ map patAtom terms

    isVar :: Term -> Bool
    isVar (Var _) = True
    isVar _       = False

-- ---------------------------------------------------------------------
-- Testing

td :: IO ()
td = do
  let (Right db) = run "a(b,c). a(x,y,z). p(X,Z) :- p(X,Y), p(Y,Z). p(X,Y) :- a(X,Y)."
  let ddb = toDatalog db
  let r = mkDb $ dlFacts ddb
  putStrLn $ "(ddb,r)=" ++ (show (ddb,r))
  return ()

tq :: IO ()
tq = do
  let (Right db) = run "a(b,c). a(X,Y) :- a(X,Y)."
  let ddb@(DL factMap ruleMap _) = toDatalog db
  let pq = tp queryP "a(b,X)."

  let edb = mkDb factMap
  -- rels <- mapM makeQueryRelation $ Map.toList ruleMap

  r <- executeQuery pq ddb
  putStrLn $ "(edb)=" ++ (show (edb))
  putStrLn $ "(ddb)=" ++ (show (ddb))
  putStrLn $ "(pq)=" ++ (show (pq))
  putStrLn $ "(r)=" ++ (show (r))
  return ()

