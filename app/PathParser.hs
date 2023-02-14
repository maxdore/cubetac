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



type AFormula = [[Id]]
type ATele = [AFormula]

data ATerm = Abs Id ATerm | App Id ATele
  deriving (Eq, Show)

data APathP = PathP Id APathP ATerm ATerm | APoint
  deriving (Eq , Show)

depth :: APathP -> Int
depth APoint = 0
depth (PathP _ ty _ _ )= 1 + depth ty


atele2tele :: Map String Int -> ATele -> Tele
atele2tele vm fs = Tele (map (\f -> Formula (map (\c -> Disj (map (\v -> Conj (vm ! v)) c)) f)) fs)

aterm2term :: Int -> Int -> Map String Int -> ATerm -> Term
aterm2term gdim cdim vm (Abs v p) = aterm2term gdim (cdim + 1) (Map.insert v cdim vm) p
aterm2term gdim cdim vm (App p rs) = -- traceShow (cdim -1 -length r) $ -- TODO INTRODUCE VARIABLES FOR ETA EQ
  -- map (\i -> Formula [Disj [Conj i]]) undefined 
  -- trace ("ASDASD_" ++ show rs ++ "@" ++ show vm ++ ":" ++ show (atele2tele vm rs) ++ "_BASD") $ 
  Term p (tele2Subst (atele2tele vm rs) (gdim-1))
  -- Term p (tele2Subst (Tele (map (map (\c -> Formula (map (\v -> Disj [Conj (vm ! v)]) c)) r) ++ [])) (gdim-1))

pathp2boundary :: APathP -> Boundary
pathp2boundary ty = pathp2boundary' (depth ty) 1 Map.empty ty
  where
  pathp2boundary' :: Int -> Int -> Map String Int -> APathP -> Boundary
  pathp2boundary' gdim cdim vm APoint = Boundary []
  pathp2boundary' gdim cdim vm (PathP v ty p q) = let vm' = Map.insert v cdim vm in
    Boundary $ (aterm2term gdim (cdim+1) vm p , aterm2term gdim (cdim+1) vm q) : faces (pathp2boundary' gdim (cdim+1) vm' ty)





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
  vars <- parseVar `sepBy1` char ' '
  spaces
  char '\8594'
  spaces
  t <- parseTerm
  return $ foldr (\v s -> Abs v s) t vars
  -- return $ Abs var t


parseDisj :: Parser AFormula
parseDisj = do
  disj <- ident `sepBy` string " ∨ "
  return [disj]

parseConj :: Parser AFormula
parseConj = do
  conj <- ident `sepBy` string " ∧ "
  return $ map singleton conj

parseDim :: Parser AFormula
parseDim =
  (ident >>= \a -> return [[ a ]]) <|>
  (between (char '(') (char ')') parseDisj) <|>
  (between (char '(') (char ')') parseConj)


parseApp :: Parser ATerm
parseApp = do
  p <- ident
  apps <- many1 (char ' ' >> parseDim) -- TODO dim instead of ident
  return $ App p apps

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
  r <- parsePath
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

test, test2, test3 , test3' , test4 , test5' :: Text
test = "zero : Interval\none : Interval\nseg : zero ≡ one\n---\none ≡ zero\n"
test2 = "zero : Interval\none : Interval\nseg : zero ≡ one\n---\nPathP (λ i → Interval) zero one\n"
test3 = "zero : Interval\none : Interval\nseg : zero ≡ one\n---\nPathP (λ i → PathP (λ _ → Interval) (seg i) one) seg (λ _ _ → one)\n"
test3' = "zero : Interval\none : Interval\nseg : zero ≡ one\n---\nPathP (λ i → PathP (λ _ → Interval) (seg i) one) (λ i → seg i) (λ _ → one)\n"
test4 = "zero : Interval\none : Interval\nseg : zero ≡ one\n---\nPathP (λ i → PathP (λ j → PathP (λ _ → Interval) (seg (i ∨ j)) (seg (i ∧ j))) (seg i) one) seg (λ _ → one)\n"

test5 = "Prelude.Sphere.a : Sphere\nPrelude.Sphere.surf : Path (a ≡ a) refl refl\n---\nPathP (λ i → PathP (λ j → PathP (λ k → PathP (λ l → PathP (λ _ → Sphere) (surf (i ∧ j ∧ k ∧ l) (i ∨ j ∨ k ∨ l)) a) (λ z → a) (λ z → a)) (λ z z → a) (λ z z → a)) (λ z z z → a) (λ z z z → a)) (λ z z z z → a) (λ z z z z → a)"
test5' = "Prelude.Sphere.a : Sphere\nPrelude.Sphere.surf : PathP (λ i → a ≡ a) (λ _ → a) (λ _ → a)\n---\nPathP (λ i → PathP (λ j → PathP (λ k → PathP (λ l → PathP (λ _ → Sphere) (surf (i ∧ j ∧ k ∧ l) (i ∨ j ∨ k ∨ l)) a) (λ z → a) (λ z → a)) (λ z z → a) (λ z z → a)) (λ z z z → a) (λ z z z → a)) (λ z z z z → a) (λ z z z z → a)"

parseAgdaProblem :: Text -> IO (Cube , Boundary)
parseAgdaProblem input =
  case parseOnly parseProblem input of
    Left err -> error $ "PARSE ERROR " ++ err
    Right (ctxt , goal) -> do
      -- print ctxt
      -- print goal
      return (Cube (map (\(p,ty) -> Decl (last (splitOn '.' p)) (pathp2boundary ty)) ctxt), pathp2boundary goal)


-- parseCube "PathP (\955 i \8594 seg i \8801 seg i) (\955 _ \8594 zero) (\955 _ \8594 one)"


