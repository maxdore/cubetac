{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Rulesets.Dede where

import qualified Data.Map as Map
import Data.Map ((!), Map)
import Data.List
import Data.Maybe

import Prel
import Poset
import Core

import Debug.Trace

-- We save formulas as tuples of conjunctions of disjunctions, and we also have
-- to keep track of which variables we could use
type Dede = (IVar , [[[IVar]]])
type PPM = PSubst

form2subst :: Dede -> Subst
form2subst (m , rs) = Map.fromList (map (\v -> (v , Vert (map (evalFormula v) rs))) (createPoset m))
  where
  evalFormula :: Vert -> [[IVar]] -> Endpoint
  evalFormula (Vert is) ds =
    let vs1 = map fst $ filter (toBool . snd) (zip [1..] is) in
    let result = map (\d -> filter (\i -> i `notElem` vs1) d) ds in
    fromBool $ [] `elem` result

subst2form :: Subst -> Dede
subst2form s =
  (domdim s , reverse $ map (\fi -> constrFormula (map (\(x , Vert is) -> (x , is !! fi)) (Map.toList s))) [0 .. coddim s-1])
    where
    constrFormula :: [(Vert , Endpoint)] -> [[IVar]]
    constrFormula ves =
      let truevs = [ v | (v , e) <- ves , toBool e ] in
      let cs = [ [ i | (e,i) <- zip vs [1..] , toBool e] | Vert vs <- truevs ] in
      let redcs = filter (\c -> not (any (\d -> c /= d && d `isSubsequenceOf` c) cs)) cs in
      let normcs = sort redcs in
        normcs


offset :: IVar -> [[[IVar]]] -> [[[IVar]]]
offset i = map (map (map (\j -> if j < i then j else j-1)))

eval :: Dede -> IVar -> Endpoint -> Dede
eval (m , rs) i e =
  let rs' = if e == I0
      then map (filter (i `notElem`)) rs
      else map (map (delete i)) rs in
  (m-1, offset i rs')

subst :: [[IVar]] -> IVar -> [[IVar]] -> [[IVar]]
subst cs i ds =
  let res = [ delete i c ++ d | c <- cs , i `elem` c , d <- ds ] ++ [ c | c <- cs , i `notElem` c ] in
    -- traceShow (cs , i , ds , res) $
    res



instance Rs Dede PPM where
  infer c t (m , r) =
    Ty m [ (i,e) +> normalise c (App t (eval (m , r) i e)) | i <- [1..m] , e <- [I0,I1] ]

  normalise c (App (App t (m , ss)) (n , rs)) =
    let rs' = map (map (map (\i -> i + m))) rs in
      -- traceShow rs' $
    let ss' = map (\s -> foldr (\i s' -> subst s' i (rs'!!(i-1))) s [1..n]) ss in
      -- traceShow ss' $
    normalise c (App t (n , map (map (map (\i -> i - m))) ss'))
  normalise c (App (Var p) (m , rs))
    -- | not (null rs) && last rs == [[m]] && not (m `elem` concat (concat (init rs)))
    --   = normalise c (App t (m-1, init rs))
    | idDim c p == m && rs == [ [[i]] | i <- [1..length rs] ] =
      -- trace ("FOUND ID" ++ show (App (Var p) (m , rs))) $
      -- trace ("FOUND ID") $
      Var p
  normalise c (App t (m , rs)) | otherwise =
      -- trace ("NORM" ++ show (App t (m , rs))) $
        let ty = inferTy c t in
        case findIndex null rs of
          Just i -> normalise c (App (getFace ty (i+1,I0)) (m , take i rs ++ drop (i+1) rs))
          Nothing -> case findIndex ([] `elem`) rs of
            Just i -> normalise c (App (getFace ty (i+1,I1)) (m , take i rs ++ drop (i+1) rs))
            Nothing -> App t (m , map (\r -> filter (\d -> not (any (\d' -> d /= d' && intersect d d' == d) r)) r) rs) -- TODO DNF

  allPTerms c d = [ PApp (Var p) (Map.fromList $ map (\v -> (v , createPoset d')) (createPoset d)) | (p , Ty d' _) <- c ]

  deg c t i = let Ty d _ = inferTy c t in
    App t (d+1 , [ [[j]] | j <- [1..d+1] , j /= i])

  unfold = (map subst2form) . getSubsts
  combine = combineSubsts . (map form2subst)


