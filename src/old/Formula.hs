module Formula where

import Data.List
import qualified Data.Map as Map

import Prel
import Data
import Poset


-- This file contains the representation of interval substitutions via elements
-- of the free distributive lattice, as well as conversions from and to the
-- representation of substitutions via poset maps


newtype Conj = Conj {literal :: IVar}
  deriving (Eq , Ord)

instance Show Conj where
  show (Conj i) = show i

newtype Disj = Disj {literals :: [Conj]}
  deriving (Eq , Ord)

instance Show Disj where
  show (Disj [i]) = show i
  show (Disj is) = "(" ++ intercalate " /\\ " (map show is) ++ ")"

newtype Formula = Formula {clauses :: [Disj]}
  deriving (Eq , Ord)

instance Show Formula where
  show (Formula [c]) = show c
  show (Formula cs) = "(" ++ intercalate " \\/ " (map show cs) ++ ")"

-- Tuples of formulas in DNF
newtype Tele = Tele {formulas :: [Formula]}
  deriving (Eq , Ord)

instance Show Tele where
  show (Tele rs) = unwords (map show rs)


-- Constructor for a 1-path with single variable application
constF :: IVar -> Tele
constF i = Tele [Formula [ Disj [Conj i]]]


-- Convert formulas to substitutions (we need to know the dimension of the domain)
tele2Subst :: Tele -> Int -> Subst
tele2Subst r gdim = Map.fromList (map (\v -> (v , evalTele r v)) (createPoset gdim))
  where
  evalTele :: Tele -> Vert -> Vert
  evalTele (Tele rs) v = Vert $ map (evalFormula v) rs

  evalFormula :: Vert -> Formula -> Endpoint
  evalFormula (Vert is) (Formula cs) =
    let vs1 = map fst $ filter (toBool . snd) (zip [1..] is) in
    let result = map (\(Disj c) -> Disj (filter (\(Conj i) -> i `notElem` vs1) c)) cs in
    Endpoint $ Disj [] `elem` result


-- Convert substitutions to formulas 
subst2Tele :: Subst -> Tele
subst2Tele s =
  Tele $ reverse $ map (\fi -> constrFormula (map (\(x , Vert is) -> (x , is !! fi)) (Map.toList s))) [0 .. coddim s-1]
    where
    constrFormula :: [(Vert , Endpoint)] -> Formula
    constrFormula ves =
      let truevs = [ v | (v , Endpoint e) <- ves , e ] in
      let cs = [ Disj [ Conj i | (Endpoint e,i) <- zip vs [1..] , e] | Vert vs <- truevs ] in
      let redcs = filter (\(Disj c) -> not (any (\(Disj d) -> c /= d && d `isSubsequenceOf` c) cs)) cs in
      let normcs = sort redcs in
        Formula normcs



dimNames :: [String]
dimNames = ["i","j","k","l","m","n","o","p","q"]

dimName :: Int -> [Int] -> String
dimName i skip = [ d | (j,d) <- zip [0..] dimNames , not (j `elem` skip) ]!!i

sparseParen int [s] = s
sparseParen int ss = "(" ++ concat (intersperse int ss) ++ ")"

agdaClause :: Disj -> [Int] -> String
agdaClause (Disj ls) skip = sparseParen " ∧ " (map (\(Conj i) -> dimName (i-1) skip) ls)

agdaFormula :: Formula -> [Int] -> String
agdaFormula (Formula cs) skip = sparseParen " ∨ " (map (\c -> agdaClause c skip) cs)


agdaAbstract :: [Int] -> String
agdaAbstract is = "\955 " ++ concat (intersperse " " (map (dimNames!!) is)) ++ " \8594 "

agdaInd :: Int -> String
agdaInd d = concat (replicate d "  ")

agdaBox :: Int -> [Int] -> Box -> String
agdaBox d skip (Box sts back) = "(" ++ agdaAbstract [d+1] ++ "\955 {\n" ++
  concatMap (\(i , (s,t)) ->
               agdaInd d ++ (if i == d-length sts+1 then "  " else "; ") ++ "(" ++
                 (dimName i []) ++ " = i0) \8594 " ++ agdaTerm (d+1) (i:skip) s ++ "\n" ++
               agdaInd d ++ "; (" ++
                 (dimName i []) ++ " = i1) \8594 " ++ agdaTerm (d+1) (i:skip) t ++ "\n")
     (zip [d-length sts+1 .. d] sts)
  ++ agdaInd d ++ "}) (" ++ agdaTerm (d+1) skip back ++ ")"


agdaTerm :: Int -> [Int] -> Term -> String
agdaTerm d skip (Term p sigma) = -- "\955 " ++ concat (intersperse " " (take (domdim sigma) dimNames)) ++ " \8594 " ++
  p ++ " "
  ++ (concat (intersperse " " (map (\f -> agdaFormula f skip) ((reverse . formulas . subst2Tele) sigma))))
agdaTerm d skip (Comp (Box sts back)) = agdaAbstract [d .. (d+length sts-1)] ++ "hcomp " ++ agdaBox (d+length sts-1) skip (Box sts back)
agdaTerm d skip (Fill (Box sts back)) = "_" -- "hfill " ++ agdaBox (d) skip (Box sts back)
agdaTerm _ skip Free = "???"

agdaShow :: Term -> String
agdaShow = agdaTerm 0 []
