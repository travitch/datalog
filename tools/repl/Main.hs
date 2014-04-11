module Main ( main ) where

import Control.Monad.Trans.Class ( lift )
import Control.Monad.Trans.State.Strict ( evalStateT, StateT, modify )
import qualified Data.Set as S
import qualified System.Console.Haskeline as HL

import Database.Datalog

import qualified Parser as P
import qualified Commands as C

main :: IO ()
main = evalStateT (HL.runInputT settings loop) s0
  where
    settings = HL.defaultSettings
    s0 = ReplState { commands = []
                   , definedRelations = S.empty
                   }

type ReplM = StateT ReplState IO

data ReplState = ReplState { commands :: [C.Command]
                           , definedRelations :: S.Set String
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
        Right (C.Query  _) -> undefined
        Right C.Quit -> return ()
        Right c -> lift $ modify $ \s -> s { commands = c : commands s }

