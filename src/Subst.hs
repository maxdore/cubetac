{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Subst where

import Data.List
import qualified Data.Map as Map
import Data.Map ((!), Map)

import Prel
import Data
import Poset


-- The alternative characterization of interval substitutions as poset maps

type Subst = Map Vert Vert

-- Get the dimensions of domain and codomain of a substitution
instance Fct Subst where
  domdim = length . toBools . fst . head . Map.toList
  coddim = length . toBools . snd . head . Map.toList


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



-- Potential substitutions have for each element in the domain a list of possible values
type PSubst = Map Vert [Vert]

instance Fct PSubst where
  domdim = length . head . Map.toList
  coddim = undefined -- TODO

-- A potential term is an identifier with potential substitution
data PTerm = PTerm Id PSubst
  deriving (Eq)

instance Show PTerm where
  show (PTerm id part) = show id ++ " " ++ show part


-- Given dimensions for domain and codomain, create the most general
-- potential substitution
createPSubst :: Int -> Int -> PSubst
createPSubst k l = Map.fromList $ map (\v -> (v , createPoset l)) (createPoset k)

-- Given a potential substitution, generate all possible substitutions from it
getSubsts :: PSubst -> [Subst]
getSubsts sigma = map Map.fromList (getSubsts' (Map.toList sigma))
  where
  getSubsts' :: [(Vert , [Vert])] -> [[(Vert , Vert)]]
  getSubsts' [] = [[]]
  getSubsts' ((x , vs) : ys) = [ (x , v) : r | v <- vs , r <- getSubsts' (filterRec x v ys) ]

  filterRec :: Vert -> Vert -> [(Vert , [Vert])] -> [(Vert , [Vert])]
  filterRec x v ys = map (\(y, us) -> (y , [ u | u <- us , (y `below` x) --> (u `below` v) ])) ys


-- Given a potential substitution, generate the substitution from it
-- (could be equivalently head of getSubsts)
fstSubst :: PSubst -> Subst
fstSubst = Map.fromList . fstPSubst' . Map.toList
  where
  fstPSubst' :: [(Vert , [Vert])] -> [(Vert , Vert)]
  fstPSubst' [] = []
  fstPSubst' ((x,vs) : yws) = (x , head vs) :
    fstPSubst' (map (\(y , ws) -> (y , filter (\w -> (y `below` x) --> (w `below` head vs)) ws)) yws)

injPSubst :: Subst -> PSubst
injPSubst = Map.map (\v -> [v])

createPTerm :: Decl -> Int -> PTerm
createPTerm (Decl id ty) gdim =
  let img = createPoset (dim ty) in
  let parts = map (\v -> (v , img)) (createPoset gdim) in
  PTerm id (Map.fromList parts)


