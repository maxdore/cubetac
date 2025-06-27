{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Rulesets.Dede where

import qualified Data.Map as Map
import Data.Map ((!), Map)
import Data.List

import Control.Monad.State

import Prel
import Poset
import Core

import Debug.Trace

-- We save formulas as tuples of conjunctions of disjunctions, and we also have
-- to keep track of which variables we could use
type Dede = (IVar , [[[IVar]]])

form2subst :: Dede -> PMap
form2subst (m , rs) = PMap $ Map.fromList (map (\v -> (v , (map (evalFormula v) rs))) (createTable m))
  where
  evalFormula :: Vert -> [[IVar]] -> Endpoint
  evalFormula (is) ds =
    let vs1 = map fst $ filter (toBool . snd) (zip [1..] is) in
    let result = map (\d -> filter (\i -> i `notElem` vs1) d) ds in
    fromBool $ [] `elem` result

subst2form :: PMap -> Dede
subst2form (PMap s) =
  (domdim (PMap s) , reverse $ map (\fi -> constrFormula (map (\(x , is) -> (x , is !! fi)) (Map.toList s))) [0 .. coddim (PMap s)-1])
    where
    constrFormula :: [(Vert , Endpoint)] -> [[IVar]]
    constrFormula ves =
      let truevs = [ v | (v , e) <- ves , toBool e ] in
      let cs = [ [ i | (e,i) <- zip vs [1..] , toBool e] | vs <- truevs ] in
      let redcs = filter (\c -> not (any (\d -> c /= d && d `isSubsequenceOf` c) cs)) cs in
      let normcs = sort redcs in
        normcs

offset :: IVar -> [[[IVar]]] -> [[[IVar]]]
offset i = map (map (map (\j -> if j < i then j else j-1)))

subst :: [[IVar]] -> IVar -> [[IVar]] -> [[IVar]]
subst cs i ds =
    -- traceShow ("SUBST" , cs , i , ds) $
  let res = [ delete i c ++ d | c <- cs , i `elem` c , d <- ds ] ++ [ c | c <- cs , i `notElem` c ] in
    -- traceShow (cs , i , ds , res) $
    res

instance Bs Dede where
  tdim (m , rs) = m
  face (m , rs) (i,e) =
    let rs' = if e == I0
                  then map (filter (i `notElem`)) rs
                  else map (map (delete i)) rs
    in (m-1, offset i rs')
  deg d i =  (d+1 , [ [[j]] | j <- [1..d+1] , j /= i])
  compose (m , ss) (n , rs) =
    -- trace "????" $
    let rs' = map (map (map (\i -> i + m))) rs in
    let ss' = map (\d -> foldr (\i d' -> subst d' i (rs'!!(i-1))) d [1..n]) ss in
    -- traceShow (ss , rs , ss') $
    (n , map (map (map (\i -> i - m))) ss')
  isId (m , rs) = rs == [ [[i]] | i <- [1..m]]
  isFace (m , rs) = case findIndex null rs of
    Just i -> Just (i+1,I0)
    Nothing -> case findIndex ([] `elem`) rs of
      Just i -> Just (i+1,I1)
      Nothing -> Nothing
  rmI (m , rs) i = (m , take (i-1) rs ++ drop i rs)

instance Rs Dede PPMap where
  allPConts _ m n = [ createPPMap m n ]
  unfold = (map subst2form) . getPMaps
  combine = PPMap . combineMaps . (map (pmap . form2subst))

  constrCont c gty (p , pty) = do
    sigma <- foldM
                  (\sigma (ie , gf) -> do
                    -- traceM $ show ie ++ " : " ++ show sigma ++ " : " ++ q ++ "<" ++ show tau ++ ">"
                    theta <- case gf of
                        App (Var q) rs | q == p -> (Just . PPMap . injPotMap . pmap) (form2subst rs)
                        _ -> do
                          let theta = filter (\s -> normalise c (App (Var p) (subst2form s)) == gf)
                                      (getPMaps (PPMap (restrMap (ppmap sigma) ie)))
                          if null theta
                            then Nothing
                            else Just ((PPMap . combineMaps . map pmap) theta)
                    return $ foldl (\s x -> updatePPMap s (insInd ie x) ((ppmap theta) ! x)) sigma (createTable (tyDim gty - 1))
                      )
                  (createPPMap (tyDim gty) (tyDim pty))
                  (sortBy (\(_, s) (_,t) -> compare (baseDim c t) (baseDim c s))
                    [ (ie , getFace gty ie) | ie <- restrictions (tyDim gty) , sideSpec gty ie])

    traceShowM (length (getPMaps sigma))
    return (App (Var p) (subst2form (fstPMap sigma)))
