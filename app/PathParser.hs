{-# LANGUAGE OverloadedStrings #-}
module PathParser where

import Data.Word
import Data.Map.Strict (Map , (!))
import qualified Data.Map.Strict as Map
import Data.Attoparsec.Text hiding (take)
import Control.Applicative
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Control.Monad.State
import Data.List

import Debug.Trace
import Prel
import Data
import Formula



type ASubst = [[Id]]

data ATerm = Abs Id ATerm | App Id ASubst
  deriving (Eq, Show)

data APathP = PathP Id APathP ATerm ATerm | APoint
  deriving (Eq , Show)

depth :: APathP -> Int
depth APoint = 0
depth (PathP _ ty _ _ )= 1 + depth ty


aterm2term :: Int -> Int -> Map String Int -> ATerm -> Term
aterm2term gdim cdim vm (Abs v p) = aterm2term gdim (cdim + 1) (Map.insert v cdim vm) p
aterm2term gdim cdim vm (App p r) = -- traceShow (cdim -1 -length r) $ -- TODO INTRODUCE VARIABLES FOR ETA EQ
  -- map (\i -> Formula [Disj [Conj i]]) undefined 
  Term p (tele2Subst (Tele ((map (\c -> Formula (map (\v -> Disj [Conj (vm ! v)]) c)) r) ++ [])) (gdim-1))

pathp2boundary :: APathP -> Boundary
pathp2boundary ty = pathp2boundary' (depth ty) 1 Map.empty ty
  where
  pathp2boundary' :: Int -> Int -> Map String Int -> APathP -> Boundary
  pathp2boundary' gdim cdim vm APoint = Boundary []
  pathp2boundary' gdim cdim vm (PathP v ty p q) = let vm' = Map.insert v cdim vm in
    Boundary $ (aterm2term gdim (cdim+1) vm p , aterm2term gdim (cdim+1) vm q) : faces (pathp2boundary' gdim cdim vm' ty)





data PState = PState Int ()

type GenParser a = StateT PState Parser a

alphaNum = letter <|> digit
spaces = skipSpace

ident = many1 (alphaNum <|> char '.')

between :: Applicative m => m open -> m close -> m a -> m a
between open close p = open *> p <* close

parseVar = many1 $ alphaNum <|> char '_'


parseAbs :: Parser ATerm
parseAbs = do
  char '\955'
  spaces
  var <- parseVar
  spaces
  char '\8594'
  spaces
  t <- parseTerm
  return $ Abs var t

parseDim :: Parser ASubst
parseDim = return []

parseApp :: Parser ATerm
parseApp = do
  p <- ident
  apps <- many (char ' ' >> ident) -- TODO dim instead of ident
  return $ App p (map (\i -> [i]) apps)

parseAtom :: Parser ATerm
parseAtom = do
  p <- ident
  return $ App p []

parseTerm :: Parser ATerm
parseTerm = 
  parseAtom <|>
  parseAbs <|>
  (between (char '(') (char ')') parseAbs) <|>
  (between (char '(') (char ')') parseApp)
  
  -- (between (char '(') (char ')')
  -- (parseAbs <|> parseBase))
  --     <|> (ident >>= \name -> return $ Face name)



parsePathP :: Parser APathP
parsePathP = do
  string "PathP "
  char '('
  char '\955'
  spaces
  var <- parseVar
  spaces
  char '\8594'
  spaces
  r <- parsePath
  char ')'
  char ' '
  -- skip isEndOfLine
  u <- parseTerm
  -- skip isEndOfLine
  skipSpace
  -- skip isEndOfLine
  v <- parseTerm
  return $ PathP var r u v


parsePathNP :: Parser APathP
parsePathNP = do
  try $ string "Path "
  r <- parsePathP
  spaces
  u <- parseTerm
  spaces
  v <- parseTerm
  return $ PathP "_" r u v

parseEq :: Parser APathP
parseEq = do
  u <- parseTerm
  spaces
  char '\8801'
  spaces
  v <- parseTerm
  return $ PathP "_" APoint u v

parsePoint :: Parser APathP
parsePoint = do
  parseVar
  return APoint

parsePath :: Parser APathP
parsePath = do
  -- traceM "try path"
  parsePathP <|> parsePathNP <|> try parseEq <|> parsePoint

parseDecl :: Parser (Id, APathP)
parseDecl = do
  var <- ident
  skipSpace
  char ':'
  skipSpace
  boundary <- parsePath
  endOfLine
  return (var, boundary)

parseProblem :: Parser ([(Id,APathP)], APathP)
parseProblem = do
  decls <- manyTill parseDecl (string "---")
  -- traceM $ show decls
  endOfLine
  -- traceM "ASD"
  goal <- parsePath
  -- traceM $ show goal
  spaces
  return (decls , goal)

test, test2, test3 :: Text
test = "zero : Interval\none : Interval\nseg : zero ≡ one\n---\none ≡ zero\n"
test2 = "zero : Interval\none : Interval\nseg : zero ≡ one\n---\nPathP (λ i → Interval) zero one\n"
test3 = "zero : Interval\none : Interval\nseg : zero ≡ one\n---\nPathP (λ i → PathP (λ _ → Interval) (seg i) one) seg (λ _ → one)\n"


parseAgdaProblem :: Text -> IO (Cube , Boundary)
parseAgdaProblem input =
  case parseOnly parseProblem input of
    Left err -> error $ "PARSE ERROR " ++ err
    Right (ctxt , goal) -> return (Cube (map (\(p,ty) -> Decl (last (splitOn '.' p)) (pathp2boundary ty)) ctxt), pathp2boundary goal)


-- parseCube "PathP (\955 i \8594 seg i \8801 seg i) (\955 _ \8594 zero) (\955 _ \8594 one)"



dimNames :: [String]
dimNames = ["i","j","k","l","m","n"]


agdaClause :: Disj -> String
agdaClause (Disj ls) = concat $ intersperse "/\\" (map (\(Conj i) -> dimNames !! (i-1)) ls)

agdaFormula :: Formula -> String
agdaFormula (Formula cs) = concat (intersperse "\\/" (map agdaClause cs))

agdaTerm :: Term -> String
-- agdaTerm (Term p sigma) = "\955 "
agdaTerm (Term p sigma) = "\955 " ++ concat (intersperse " " (take (domdim sigma) dimNames)) ++ " \8594 " ++ p ++ " " ++ (concat (intersperse " " (map agdaFormula ((formulas . subst2Tele) sigma))))

