{-# LANGUAGE OverloadedStrings #-}
module Parser where

import Data.Word
import Data.Attoparsec.Text
import Control.Applicative
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

import Debug.Trace
import Data
import Formula

parseId = many1 (letter <|> digit)

parseDecl :: Parser Decl
parseDecl = do
  var <- parseId
  skipSpace
  char ':'
  skipSpace
  boundary <- parseBoundary
  endOfLine
  return $ Decl var boundary

parseBoundary :: Parser Boundary
parseBoundary = do
  char '['
  fgs <- parseTermPair `sepBy` char ','
  char ']'
  let facedim = length fgs - 1
  return $ Boundary (map (\((f , r),(g , s)) -> (Term f (tele2Subst r facedim) , Term g (tele2Subst s facedim)) ) fgs)

type FTerm = (Id , Tele)

parseTermPair :: Parser (FTerm , FTerm)
parseTermPair = do
  skipSpace
  char '('
  skipSpace
  f <- parseTerm
  skipSpace
  char ','
  skipSpace
  g <- parseTerm
  skipSpace
  char ')'
  skipSpace
  return (f , g)


parseTerm :: Parser FTerm
parseTerm = do
  var <- parseId
  tele <- many parseFormula
  return (var , Tele tele)

parseFormula :: Parser Formula
parseFormula = do
  char ' '
  parseClauses <|> (decimal >>= \i -> return $ Formula [Disj [Conj i]])

parseClauses :: Parser Formula
parseClauses = do
  char '('
  disj <- parseDisj `sepBy1` string " \\/ "
  char ')'
  return $ Formula disj

parseDisj :: Parser Disj
parseDisj = do
  (decimal >>= \i -> return $ Disj [Conj i]) <|> parseLiterals

parseLiterals :: Parser Disj
parseLiterals = do
  char '('
  conj <- (decimal >>= \i -> return $ Conj i) `sepBy1` string " /\\ "
  char ')'
  return $ Disj conj


parseGoal :: Parser (Id , Boundary)
parseGoal = do
  many1 endOfLine
  gid <- parseId
  skipSpace
  char '='
  skipSpace
  goal <- parseBoundary
  return (gid , goal)

fileParser :: Parser (Cube , [(Id , Boundary)])
fileParser = do
  decls <- manyTill parseDecl (string "---")
  goals <- many' parseGoal
  return (Cube decls , goals)

loadExample :: String -> IO (Cube, [(Id , Boundary)])
loadExample filename = do
  file <- TIO.readFile filename
  print file
  case parseOnly fileParser file of
    Right res -> return res
    Left err -> error $ "Could not parse file" ++ err
