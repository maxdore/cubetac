module Deg where

import Data.List
import qualified Data.Map as Map
import Data.Map ((!), Map)

import Prel
import Data



-- Substitutions to formulas

evalFormula :: Vert -> Formula -> Endpoint
evalFormula (Vert is) (Formula cs) =
  -- let vs0 = map fst $ filter (\(v , Endpoint e) -> not e) (zip [1..] is) in
  let vs1 = map fst $ filter (toBool . snd) (zip [1..] is) in
  let result = map (\(Disj c) -> Disj (filter (\(Conj i) -> not (i `elem` vs1)) c)) cs in
  Endpoint $ Disj [] `elem` result

evalTele :: Tele -> Vert -> Vert
evalTele (Tele rs) v = Vert $ map (evalFormula v) rs

formula2Subst :: Tele -> Int -> Subst
formula2Subst r gdim = Map.fromList (map (\v -> (v , evalTele r v)) (createGrid gdim))


-- Formulas to substitutions

constrFormula :: [(Vert , Endpoint)] -> Formula
constrFormula ves =
  let truevs = [ v | (v , Endpoint e) <- ves , e ] in -- filter (toBool . snd) ves in
  let cs = [ Disj [ Conj i | (Endpoint e,i) <- (zip vs [1..]) , e] | Vert vs <- truevs ] in
  let redcs = filter (\(Disj c) -> not (any (\(Disj d) -> c /= d && d `isSubsequenceOf` c) cs)) cs in
  let normcs = sort redcs in
    Formula normcs

subst2Tele :: Subst -> Tele
subst2Tele s =
  let nvs = domdim s in
  let nfs = coddim s in
  Tele $ map (\fi -> constrFormula (map (\(x , Vert is) -> (x , is !! fi)) (Map.toList s))) [0 .. nfs-1]



createGrid :: Int -> [Vert]
createGrid 0 = [Vert []]
createGrid n = let g = map toBools (createGrid (n - 1))
  in map (\v -> Vert (e0 : v)) g ++ map (\v -> Vert (e1 : v)) g


-- Order: for each 1 index, all with 1 in it are below
below , above :: Vert -> Vert -> Bool
x `below` y = all (\(e , e') -> toBool e' --> toBool e) (zip (toBools x) (toBools y))
x `above` y = y `below` x

