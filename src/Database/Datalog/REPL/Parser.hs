{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

-- |Parse Datalog statements and convert them to internal representation

module Database.Datalog.REPL.Parser
{-
    (
      statements
    , Env(..)
    , initialEnv
    , P
    ) -} where


import qualified Data.Text as T
import Data.Text (Text)

import qualified Data.Map as M
import Data.Map (Map)

import Control.Applicative ((<$>))
import Control.Monad.State

import Data.Either (partitionEithers)

import Text.Parsec.Combinator
import Text.Parsec.Prim hiding (State)
import Text.Parsec.Error
import Text.Parsec.Char

import Database.Datalog.REPL.Backend

type P = Parsec Text Env

instance (Monad m) => Stream Text m Char where
    uncons = return . T.uncons

data Env = Env 
    { envConMap :: Map String Con
    , envNextFree :: !Id
    } deriving (Show)

initialEnv :: Env
initialEnv = Env { envNextFree = 0, envConMap = M.empty } 

fresh :: P Int
fresh = do
    env <- getState
    let free = envNextFree env
    putState $ env { envNextFree = free + 1 }
    return free

mkCon :: String -> P Con
mkCon k = do
    m <- envConMap <$> getState
    case M.lookup k m of
        Just c -> return c
        Nothing -> do
            i <- fresh
            let result = C i k
            modifyState $ \env -> env { envConMap = M.insert k result m } 
            return result

-- parser

word :: P String
word = many1 letter

var :: P Var
var = do
    l <- upper <?> "variable"
    ls <- many letter
    return $ V (l:ls)

con :: P Con
con = do
    u <- lower <?> "constructor"
    us <- many letter
    mkCon (u:us)

neg :: P ()
neg = (string "\\+" <|> string "~") >> return ()

term :: P Term
term =  Var <$> var 
    <|> Con <$> con


turnstile :: P ()
turnstile = string ":-" >> return ()

period :: P ()
period = char '.' >> return ()

comma :: P ()
comma = char ',' >> return ()

open :: P ()
open = (char '(' >> spaces >> return ()) <?> "("

close :: P ()
close = (spaces >> char ')' >> return ()) <?> ")"

betweenParens :: P a -> P a
betweenParens = between open close 

spaced :: P a -> P a
spaced = between spaces spaces

atom :: P a -> P (Atom a)
atom t = do
    pred <- con
    Atom pred <$> (betweenParens (t `sepBy` spaced comma) <|> return [])
  <?> "atom"

pat :: P Pat
pat = do { neg; spaces; Not <$> atom term } <|> Pat <$> atom term
          
fact :: P (Atom Con)
fact = atom con
  <?> "fact"

queryP :: P (Atom Term)
queryP = spaced (atom term)
  <?> "query"

rule :: P Rule
rule = do
    head <- atom term
    spaced turnstile <?> ":-"
    -- body <- pat `sepBy` many1 space
    body <- pat `sepBy` spaced comma
    safe $ Rule head body
  <?> "rule"

safe :: Rule -> P Rule
safe rule@(Rule head body) = do
        forM_ headVars $ \v -> 
            when (v `notElem` bodyVars) $ do
                unexpected $ "variable " ++ show (varName v) ++ " appears in head, but not occur positively in body"
        forM_ subVars $ \v -> 
            when (v `notElem` bodyVars) $ do
                unexpected $ "variable " ++ show (varName v) ++ " appears in a negated subgoal, but not occur positively in body"
        return rule
    where
        headVars, bodyVars, subVars :: [Var]
        headVars = [ v | Var v <- atomArgs head ]
        bodyVars = concatMap posVars body
        subVars  = concatMap negVars body

        posVars, negVars :: Pat -> [Var]
        posVars (Pat atom) = [ v | Var v <- atomArgs atom ]
        posVars (Not _) = []
        negVars (Not atom) = [ v | Var v <- atomArgs atom ]
        negVars (Pat _) = []

statement :: P (Either Fact Rule)
statement = try (Left <$> fact)
            <|> (Right <$> rule) 
lineSep :: P ()
lineSep = spaced period <?> "."

statements :: P ([Fact],[Rule])
statements = do 
    spaces
    result <- partitionEithers <$> statement `sepEndBy` lineSep
    eof
    return result

run :: String -> Either ParseError ([Fact],[Rule])
run = runParser statements initialEnv "-" . T.pack

-- ---------------------------------------------------------------------
-- Test stuff

tp parser xs = case runParser parser initialEnv "-" (T.pack xs) of
    Left msg -> error $ "[parser] " ++ (show msg)
    Right x -> x

t = run "x(B,C) :- a(B,C), a(B,c)."

