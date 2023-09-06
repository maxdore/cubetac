{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Poset where

import qualified Data.Map as Map
import Data.Map ((!), Map)
import Data.List
import Data.Maybe

import Prel
import Core



-- An element of a poset is a list of 0s and 1s
newtype Vert = Vert { toBools :: [Endpoint]}
  deriving (Eq , Ord)

instance Show Vert where
  show (Vert []) = "()"
  show (Vert es) = concatMap (\e -> if e == I0 then "0" else "1") es
  -- show (Vert es) = "(" ++ concatMap (\e -> if e == I0 then "0" else "1") es ++ ")"

type Poset = [Vert]

-- Construct I^n poset
createPoset :: Int -> Poset
createPoset n | n <= 0 = [Vert []]
createPoset n = let g = map toBools (createPoset (n - 1))
  in map (\v -> Vert (I0 : v)) g ++ map (\v -> Vert (I1 : v)) g


baseVert :: Int -> Int -> Vert
baseVert n i = Vert (replicate (i-1) I0 ++ [I1] ++ replicate (n-i) I0)

-- Construct poset that only has one connective
create1ConnPoset :: Int -> Poset
create1ConnPoset n = -- Vert (replicate n I0) :
  map (baseVert n) [1..n]


-- Checking order between two elements of a poset
below , above :: Vert -> Vert -> Bool
x `below` y = all (\(e , e') -> toBool e' --> toBool e) (zip (toBools x) (toBools y))
x `above` y = y `below` x


-- Given an element in a poset, remove the i-th index from it
removeInd :: Vert -> Int -> Vert
removeInd (Vert (_:es)) 1 = Vert es
removeInd (Vert (e:es)) n = Vert (e : toBools (removeInd (Vert es) (n-1)))
removeInd _ _ = error "This index is not part of the element"

-- Insert e such that x_i = e afterwards
insInd :: Restr -> Vert -> Vert
insInd (0 , _) _ = error "Indices start from 1"
insInd (i , e) (Vert es) | i > length es + 1 = error "Index too large for element"
                     | otherwise = let (f,s) = splitAt (i-1) es in Vert (f ++ [e] ++ s)

-- Given a list of vertices, return the first index at which all vertices
-- have the same value, as well as that value
getFirstCommon :: [Vert] -> (Int , Endpoint)
getFirstCommon vs
  | all ((== I1) . head . toBools) vs = (1 , I1)
  | all ((== I0) . head . toBools) vs = (1 , I0)
  | otherwise = let (i , e) = getFirstCommon (map (Vert . tail . toBools) vs) in (i + 1 , e)

getAllCommon :: [Vert] -> [(Int , Endpoint)]
getAllCommon vs = if length vs > length (toBools (head vs)) -- TODO NOT CORRECT
  then []
  else
    let (i,e) = getFirstCommon vs in
    (i,e) : map (\(j,e') -> (j+ 1, e')) (getAllCommon (map (\v -> removeInd v i) vs))



-- Given a list of n^2 elements of a poset, generate map from [1]^n to the elements
reconstrPMap :: [Vert] -> Map Vert Vert
reconstrPMap vs = Map.fromList (zip (createPoset (log2 (length vs))) vs)


-- We regard interval substitutions as poset maps
type Subst = Map Vert Vert

-- Get the dimensions of domain and codomain of a substitution
instance Fct Subst where
  domdim = length . toBools . fst . head . Map.toList
  coddim = length . toBools . snd . head . Map.toList

type PSubst = Map Vert [Vert]

instance Fct PSubst where
  domdim = length . toBools . fst . head . Map.toList
  coddim = length . toBools . head . snd . head . Map.toList

createPSubst :: Int -> Int -> PSubst
createPSubst k l = Map.fromList $ map (\v -> (v , createPoset l)) (createPoset k)

create1ConnPSubst :: Int -> Int -> PSubst
create1ConnPSubst m n = Map.fromList (map (\x -> (x , createPoset n)) (create1ConnPoset m))

-- Give back restriction of sigma and forget that it was a restriction
restrPSubst :: PSubst -> Restr -> PSubst
restrPSubst sigma (i,e) = Map.mapKeys (`removeInd` i) (Map.filterWithKey (\x _ -> e == toBools x !! (i-1)) sigma)

-- Given a potential substitution, generate all possible substitutions from it
getSubsts :: PSubst -> [Subst]
getSubsts sigma = map Map.fromList (getSubsts' (Map.toList sigma))
  where
  getSubsts' :: [(Vert , [Vert])] -> [[(Vert , Vert)]]
  getSubsts' [] = [[]]
  getSubsts' ((x , vs) : ys) = [ (x , v) : r | v <- vs , r <- getSubsts' (filterRec x v ys) ]

  filterRec :: Vert -> Vert -> [(Vert , [Vert])] -> [(Vert , [Vert])]
  filterRec x v = map (\(y, us) -> (y , [ u | u <- us , (y `below` x) --> (u `below` v) ]))

combineSubsts :: [Subst] -> PSubst
combineSubsts ss = Map.mapWithKey (\x _ -> nub (map (Map.findWithDefault undefined x) ss)) (head ss)
  --Map.fromList (map (\x -> (x , nub (map (Map.findWithDefault undefined x) ss))) (createPoset (domdim (head ss))))

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
injPSubst = Map.map (: [])

-- updateGadgets :: PSubst -> [Subst] -> [Restr] -> PSubst
-- updateGadgets sigma ss ies =
--   let xs = createPoset (domdim sigma) in
--   let vus = map (\x -> nub (map (! x) ss)) xs in -- TODO TAKE INTO ACCOUNT RESTRICTIONS!
--   foldl (\s (x , vu) -> updatePSubst s x vu) sigma (zip xs vus)

updatePSubst :: PSubst -> Vert -> [Vert] -> PSubst
updatePSubst sigma x vs = Map.mapWithKey (\y us -> filter (\u ->
                                                        (y `above` x) --> any (u `above`) vs &&
                                                        (y `below` x) --> any (u `below`) vs
                                                      ) us) (Map.insert x vs sigma)


