{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Main ( main ) where

import qualified Control.Monad.Catch as E
import Control.Monad.Trans.Class ( lift )
import Control.Monad.Trans.State.Strict ( evalStateT, StateT, modify, gets )
import qualified Data.Foldable as F
import qualified Data.List as L
import qualified Data.Map as M
import Data.Sequence ( Seq, (|>) )
import qualified Data.Sequence as Seq
import qualified Data.Set as S
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

clauseString :: C.Clause C.LiteralValue -> String
clauseString (C.Clause name lits) = printf "%s(%s)" name strs
  where
    strs = L.intercalate ", " $ map litToString lits

litToString :: C.LiteralValue -> String
litToString (C.LVString s) = s

pleatM :: (Monad m, F.Foldable f) => a -> f b -> (a -> b -> m a) -> m a
pleatM seed elts f = F.foldlM f seed elts

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
    _ <- pleatM M.empty cs $ \c -> do
      undefined
    return undefined -- Make the query here

data EvaluationError = ArityMismatch Int (C.Clause C.LiteralValue)
                     deriving (Eq, Ord, Show, Typeable)

instance E.Exception EvaluationError
