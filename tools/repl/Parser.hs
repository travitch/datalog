{-# LANGUAGE PatternGuards #-}
module Parser ( parseInput ) where

import Control.Applicative
import Control.Monad ( void )
import Data.Maybe ( mapMaybe )
import qualified Text.Parsec as P

import Commands ( Command )
import qualified Commands as C

type Parser = P.Parsec String ()

token :: Parser a -> Parser a
token = (P.spaces *>)

parseInput :: String -> Either P.ParseError Command
parseInput = P.runParser commandParser () "<repl>"

startCommand :: Parser ()
startCommand = void $ token (P.char ':')

pCommand :: Parser Command
pCommand = do
  startCommand
  P.choice [ C.DumpFacts <$ P.string "facts"
           ]

relationName :: Parser String
relationName = do
  c <- P.lower
  cs <- P.many P.alphaNum
  return (c:cs)

variable :: Parser C.AnyValue
variable = C.AVVariable <$> P.many1 P.upper

literal :: Parser C.AnyValue
literal = (C.AVLiteral . C.LVString) <$> relationName

argument :: Parser C.AnyValue
argument = variable <|> literal

clause :: Parser (C.Clause C.AnyValue)
clause = do
  rel <- token relationName
  _ <- token (P.char '(')
  args <- token argument `P.sepBy` comma
  _ <- token (P.char ')')
  return $ C.Clause rel args
  where
    comma = token (P.char ',')

pAssertFact :: Parser Command
pAssertFact = do
  C.Clause r args <- clause
  _ <- token (P.char '.')
  litArgs <- asLiteral args
  return $ C.AssertFact $ C.Clause r litArgs

pQuery :: Parser Command
pQuery = do
  c <- clause
  _ <- token (P.char '?')
  return $ C.Query c

pAddRule :: Parser Command
pAddRule = do
  r <- clause
  _ <- token (P.string ":-")
  cs <- token clause `P.sepBy` comma
  _ <- token (P.char '.')
  return $ C.AddRule r cs
  where
    comma = token (P.char ',')

commandParser :: Parser C.Command
commandParser =
  P.choice [ pCommand
           , pAssertFact
           , pQuery
           , pAddRule
           ]

asLiteral :: [C.AnyValue] -> Parser [C.LiteralValue]
asLiteral args
  | all isLiteral args = return $ mapMaybe toLiteral args
  | otherwise = P.unexpected "Asserted a fact with a non-literal argument"
  where
    isLiteral (C.AVVariable _) = False
    isLiteral (C.AVLiteral _) = True
    toLiteral (C.AVLiteral s) = Just s
    toLiteral _ = Nothing
