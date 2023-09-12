{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Poset where

import qualified Data.Map as Map
import Data.Map ((!),Map)
import Data.List

import Prel
import Core

-- An element of a poset is a list of 0s and 1s
type Vert = [Endpoint]

type Poset = [Vert]

-- Construct I^n poset
createPoset :: Int -> Poset
createPoset n | n <= 0 = [[]]
createPoset n = let g = (createPoset (n - 1))
  in map (I0 :) g ++ map (I1 :) g

-- Construct x in I^n such that x_i = 1 and 0 otherwise
baseVert :: Int -> Int -> Vert
baseVert n i = (replicate (i-1) I0 ++ [I1] ++ replicate (n-i) I0)

-- Construct poset which determines formulas with 1 connective
create1ConnPoset :: Int -> Poset
create1ConnPoset n = (replicate n I0) : map (baseVert n) [1..n]

-- Given an element in a poset, remove the i-th index from it
rmInd :: Vert -> Int -> Vert
rmInd ((_:es)) 1 = es
rmInd ((e:es)) n = e : (rmInd es (n-1))
rmInd _ _ = error "This index is not part of the element"

-- Insert e such that x_i = e afterwards
insInd :: Restr -> Vert -> Vert
insInd (0 , _) _ = error "Indices start from 1"
insInd (i , e) es | i > length es + 1 = error "Index too large for element"
                  | otherwise = let (f,s) = splitAt (i-1) es in (f ++ [e] ++ s)

-- Checking order between two elements of a poset
below , above :: Vert -> Vert -> Bool
x `below` y = all (\(e , e') -> toBool e' --> toBool e) (zip x y)
x `above` y = y `below` x

-- The type of poset maps
type PMap = Map Vert Vert

instance Fct PMap where
  domdim = length . fst . head . Map.toList
  coddim = length . snd . head . Map.toList

-- The type of potential poset maps
type PPMap = Map Vert [Vert]

instance Fct PPMap where
  domdim = length . fst . head . Map.toList
  coddim = length . head . snd . head . Map.toList

createPPMap :: Int -> Int -> PPMap
createPPMap k l = Map.fromList $ map (\v -> (v , createPoset l)) (createPoset k)

create1ConnPPMap :: Int -> Int -> PPMap
create1ConnPPMap m n = Map.fromList (map (\x -> (x , createPoset n)) (create1ConnPoset m))

-- Give back restriction of sigma, where also domain is restricted
restrPMap :: PMap -> Restr -> PMap
restrPMap sigma (i,e) = Map.mapKeys (`rmInd` i) (Map.filterWithKey (\x _ -> e == x !! (i-1)) sigma)
restrPPMap :: PPMap -> Restr -> PPMap
restrPPMap sigma (i,e) = Map.mapKeys (`rmInd` i) (Map.filterWithKey (\x _ -> e == x !! (i-1)) sigma)

-- Given a potential substitution, generate all possible substitutions from it
getPMaps :: PPMap -> [PMap]
getPMaps sigma = map Map.fromList (getPMaps' (Map.toList sigma))
  where
  getPMaps' :: [(Vert , [Vert])] -> [[(Vert , Vert)]]
  getPMaps' [] = [[]]
  getPMaps' ((x , vs) : ys) = [ (x , v) : r | v <- vs , r <- getPMaps' (filterRec x v ys) ]

  filterRec :: Vert -> Vert -> [(Vert , [Vert])] -> [(Vert , [Vert])]
  filterRec x v = map (\(y, us) -> (y , [ u | u <- us , (y `below` x) --> (u `below` v) ]))

combinePMaps :: [PMap] -> PPMap
combinePMaps ss = Map.mapWithKey (\x _ -> nub (map (! x) ss)) (head ss)

-- Given a potential substitution, generate the substitution from it
-- (equivalent to head of getPMaps, but perhaps more efficient)
fstPMap :: PPMap -> PMap
fstPMap = Map.fromList . fstPPMap' . Map.toList
  where
  fstPPMap' :: [(Vert , [Vert])] -> [(Vert , Vert)]
  fstPPMap' [] = []
  fstPPMap' ((x,vs) : yws) = (x , head vs) :
    fstPPMap' (map (\(y , ws) -> (y , filter (\w -> (y `below` x) --> (w `below` head vs)) ws)) yws)

injPPMap :: PMap -> PPMap
injPPMap = Map.map (: [])

updatePPMap :: PPMap -> Vert -> [Vert] -> PPMap
updatePPMap sigma x vs = Map.mapWithKey
  (\y us -> filter (\u ->
              (y `above` x) --> any (u `above`) vs &&
              (y `below` x) --> any (u `below`) vs
            ) us) (Map.insert x vs sigma)


