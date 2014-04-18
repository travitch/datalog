{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
module Main ( main ) where

import qualified Control.Monad.Catch as E
import Control.Monad.Trans.Class ( lift )
import Control.Monad.Trans.State.Strict ( evalStateT, StateT, modify, gets )
import qualified Data.Foldable as F
import qualified Data.List as L
import qualified Data.Map as M
import Data.Sequence ( Seq, (|>) )
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import Data.Typeable ( Typeable )
import qualified System.Console.Haskeline as HL
import Text.Printf ( printf )

import Database.Datalog

import qualified Parser as P
import qualified Commands as C

main :: IO ()
main = evalStateT (HL.runInputT settings loop) s0
  where
    settings = HL.defaultSettings
    s0 = ReplState { commands = Seq.empty
                   , definedRelations = M.empty
                   }

type ReplM = StateT ReplState IO

data ReplState = ReplState { commands :: !(Seq C.Command)
                           , definedRelations :: !(M.Map String Int)
                           }

-- Each time a (non-query) command is entered, just record it in the
-- list.  If the command is a query, then "interpret" the whole list
-- of commands as a DatabaseBuilder action and run it to produce a
-- Database.  Then execute the query.  Displaying facts is just a
-- filter over the list of commands.

loop :: HL.InputT ReplM ()
loop = do
  minput <- HL.getInputLine "% "
  case minput of
    Nothing -> return ()
    Just input -> do
      let cmd = P.parseInput input
      case cmd of
        Left err -> HL.outputStrLn (show err) >> loop
        Right C.DumpFacts -> do
          cs <- lift $ gets commands
          F.forM_ cs $ \c ->
            case c of
              C.AssertFact cl -> HL.outputStrLn (clauseString cl)
              _ -> return ()
          loop
        Right C.DumpRules -> do
          cs <- lift $ gets commands
          F.forM_ cs $ \c -> do
            case c of
              C.AddRule ruleHead ruleBody -> HL.outputStrLn (ruleString ruleHead ruleBody)
              _ -> return ()
          loop
        Right (C.Query qc@(C.Clause name _)) -> do
          erows <- lift $ E.try (evaluateQuery qc)
          case erows of
            Left err -> do
              let errAs :: EvaluationError
                  errAs = err
              HL.outputStrLn (show errAs)
              loop
            Right rows -> do
              F.forM_ rows $ \row -> do
                let s = L.intercalate ", " row
                HL.outputStrLn $ printf "%s(%s)" name s
              loop
        Right C.Quit -> return ()
        Right c -> do
          lift $ modify $ \s -> s { commands = commands s |> c }
          loop

ruleString :: C.Clause C.AnyValue -> [C.Clause C.AnyValue] -> String
ruleString ruleHead ruleBody =
  concat [ cstring ruleHead
         , " :- "
         , L.intercalate ", " (map cstring ruleBody)
         ]
  where
    cstring (C.Clause name args) =
      let strs = L.intercalate ", " $ map valToString args
      in printf "%s(%s)" name strs
    valToString (C.AVVariable s) = s
    valToString (C.AVLiteral (C.LVString s)) = s

clauseString :: C.Clause C.LiteralValue -> String
clauseString (C.Clause name lits) = printf "%s(%s)" name strs
  where
    strs = L.intercalate ", " $ map litToString lits

litToString :: C.LiteralValue -> String
litToString (C.LVString s) = s

pleatM :: (Monad m, F.Foldable f) => a -> f b -> (a -> b -> m a) -> m a
pleatM seed elts f = F.foldlM f seed elts

evaluateQuery :: C.Clause C.AnyValue -> StateT ReplState IO [[String]]
evaluateQuery (C.Clause name vals) = do
  cs <- gets commands
  db <- makeDatabase $ do
    _ <- pleatM M.empty cs $ \ !a c -> do
      case c of
        C.AssertFact fact@(C.Clause rel factVals) ->
          case M.lookup rel a of
            Nothing -> do
              let arity = length factVals
              r <- addRelation (T.pack rel) arity
              assertFact r (map litToString factVals)
              lift $ modify $ \s -> s { definedRelations = M.insert rel arity (definedRelations s) }
              return $ M.insert rel (r, arity) a
            Just (r, arity) | arity == length factVals -> do
              assertFact r (map litToString factVals)
              return a
            Just (_, arity) -> E.throwM $ ArityMismatch arity fact
        _ -> return a
    return ()
  queryDatabase db $ do
    _ <- pleatM M.empty cs $ \ !a c -> do
      case c of
        C.AddRule h@(C.Clause headRel headVals) body -> do
          a1 <- checkArityDefs a h
          a2 <- F.foldlM checkArityDefs a1 body
          hr <- inferencePredicate (T.pack headRel)
          let headTerms = map toTerm headVals
              bodies = map toBodyClause body
          assertRule (hr, headTerms) bodies
          return a2
        _ -> return a
    qrel <- inferencePredicate (T.pack name)
    issueQuery qrel (map toTerm vals)

toBodyClause :: C.Clause C.AnyValue -> QueryBuilder ReplM String (Literal Clause String)
toBodyClause c@(C.Clause rel vals) = do
  checkArity c
  r <- inferencePredicate (T.pack rel)
  lit r (map toTerm vals)

toTerm :: C.AnyValue -> Term String
toTerm (C.AVVariable v) = LogicVar (T.pack v)
toTerm (C.AVLiteral (C.LVString l)) = Atom l

checkArityDefs :: M.Map String (Relation, Int)
                  -> C.Clause C.AnyValue
                  -> QueryBuilder ReplM String (M.Map String (Relation, Int))
checkArityDefs defs c@(C.Clause rel vals) = do
  checkArity c
  case M.lookup rel defs of
    Nothing -> do
      r <- inferencePredicate (T.pack rel)
      return $ M.insert rel (r, length vals) defs
    Just (_, arity) | arity == length vals -> return defs
                    | otherwise -> E.throwM $ ArityMismatch2 arity c

checkArity :: C.Clause C.AnyValue -> QueryBuilder ReplM String ()
checkArity c@(C.Clause rel vals) = do
  rs <- lift $ gets definedRelations
  case M.lookup rel rs of
    Just arity | carity == arity -> return ()
               | otherwise -> E.throwM $ ArityMismatch2 arity c
    Nothing -> lift $ modify $ \s -> s { definedRelations = M.insert rel carity (definedRelations s) }
  where
    carity = length vals

data EvaluationError = ArityMismatch Int (C.Clause C.LiteralValue)
                     | ArityMismatch2 Int (C.Clause C.AnyValue)
                     deriving (Eq, Ord, Show, Typeable)

instance E.Exception EvaluationError
