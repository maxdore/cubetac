module Formula where

import Data.List
import qualified Data.Map as Map
import Data.Map ((!), Map)

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
  show (Disj is) = "(" ++ (concat $ intersperse " /\\ " (map show is)) ++ ")"

newtype Formula = Formula {clauses :: [Disj]}
  deriving (Eq , Ord)

instance Show Formula where
  show (Formula cs) = "(" ++ (concat $ intersperse " \\/ " (map show cs)) ++ ")"

-- Tuples of formulas in DNF
newtype Tele = Tele {formulas :: [Formula]}
  deriving (Eq , Ord)

instance Show Tele where
  show (Tele rs) = concat $ intersperse " " (map show rs)


-- Constructor for a 1-path with single variable application
constF :: IVar -> Tele
constF i = Tele [Formula [ Disj [Conj i]]]


-- Convert substitutions to formulas (we need to know the dimension of the domain)
tele2Subst :: Tele -> Int -> Subst
tele2Subst r gdim = Map.fromList (map (\v -> (v , evalTele r v)) (createPoset gdim))
  where
  evalTele :: Tele -> Vert -> Vert
  evalTele (Tele rs) v = Vert $ map (evalFormula v) rs

  evalFormula :: Vert -> Formula -> Endpoint
  evalFormula (Vert is) (Formula cs) =
    let vs1 = map fst $ filter (toBool . snd) (zip [1..] is) in
    let result = map (\(Disj c) -> Disj (filter (\(Conj i) -> not (i `elem` vs1)) c)) cs in
    Endpoint $ Disj [] `elem` result


-- Convert formulas to substitutions
subst2Tele :: Subst -> Tele
subst2Tele s =
  let nvs = domdim s in
  let nfs = coddim s in
  Tele $ map (\fi -> constrFormula (map (\(x , Vert is) -> (x , is !! fi)) (Map.toList s))) [0 .. nfs-1]
    where
    constrFormula :: [(Vert , Endpoint)] -> Formula
    constrFormula ves =
      let truevs = [ v | (v , Endpoint e) <- ves , e ] in
      let cs = [ Disj [ Conj i | (Endpoint e,i) <- (zip vs [1..]) , e] | Vert vs <- truevs ] in
      let redcs = filter (\(Disj c) -> not (any (\(Disj d) -> c /= d && d `isSubsequenceOf` c) cs)) cs in
      let normcs = sort redcs in
        Formula normcs


