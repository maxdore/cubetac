{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Poset where

import qualified Data.Map as Map
import Data.Map ((!),Map)
import Data.List

import Prel
import Core

type Vert = [Endpoint]

type Table = [Vert]

-- Construct I^n poset
createTable :: Int -> Table
createTable n | n <= 0 = [[]]
createTable n = let g = (createTable (n - 1))
  in map (I0 :) g ++ map (I1 :) g

-- Construct x in I^n such that x_i = 1 and 0 otherwise
baseVert :: Int -> Int -> Vert
baseVert n i = (replicate (i-1) I0 ++ [I1] ++ replicate (n-i) I0)

-- Construct poset which determines formulas with 1 connective
create1ConnTable :: Int -> Table
create1ConnTable n = (replicate n I0) : map (baseVert n) [1..n]

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


-- Give back restriction of sigma, where also domain is restricted
restrMap :: Map Vert a -> Restr -> Map Vert a
restrMap sigma (i,e) = Map.mapKeys (`rmInd` i) (Map.filterWithKey (\x _ -> e == x !! (i-1)) sigma)


combineMaps :: Ord a => Eq b => [Map a b] -> Map a [b]
combineMaps ss = Map.mapWithKey (\x _ -> nub (map (! x) ss)) (head ss)


injPotMap :: Map a b -> Map a [b]
injPotMap = Map.map (: [])


isFaceSet :: [Vert] -> Maybe Restr
isFaceSet vs
  | null (head vs) = Nothing
  | all ((== I1) . head) vs = Just (1 , I1)
  | all ((== I0) . head) vs = Just (1 , I0)
  | otherwise = case isFaceSet (map tail vs) of
      Nothing -> Nothing
      Just (i , e) -> Just (i + 1 , e)



-- for Boolean/DeMorgan

newtype TruthTable = TruthTable {tt :: Map Vert Vert} deriving (Eq,Show,Ord)

instance Fct TruthTable where
  domdim = length . fst . head . Map.toList . tt
  coddim = length . snd . head . Map.toList . tt

-- The type of potential poset maps
newtype PTruthTable = PTruthTable {ptt :: Map Vert [Vert]} deriving (Eq,Show,Ord)

instance Fct PTruthTable where
  domdim = length . fst . head . Map.toList . ptt
  coddim = length . head . snd . head . Map.toList . ptt

createPTruthTable :: Int -> Int -> PTruthTable
createPTruthTable k l = PTruthTable $ Map.fromList $ map (\v -> (v , createTable l)) (createTable k)

getTruthTables :: PTruthTable -> [TruthTable]
getTruthTables (PTruthTable sigma) = map (TruthTable . Map.fromList) (helper (Map.toList sigma))
  where
  helper :: [(Vert , [Vert])] -> [[(Vert , Vert)]]
  helper [] = [[]]
  helper ((x , vs) : ys) = [ (x , v) : r | v <- vs , r <- helper ys ]

updatePTruthTable :: PTruthTable -> Vert -> [Vert] -> PTruthTable
updatePTruthTable (PTruthTable sigma) x vs = PTruthTable $ Map.insert x vs sigma



-- Poset specific

-- The type of poset maps
newtype PMap = PMap {pmap :: Map Vert Vert} deriving (Eq,Show,Ord)

instance Fct PMap where
  domdim = length . fst . head . Map.toList . pmap
  coddim = length . snd . head . Map.toList . pmap

-- The type of potential poset maps
newtype PPMap = PPMap {ppmap :: Map Vert [Vert]} deriving (Eq,Show,Ord)

instance Fct PPMap where
  domdim = length . fst . head . Map.toList . ppmap
  coddim = length . head . snd . head . Map.toList . ppmap

createPPMap :: Int -> Int -> PPMap
createPPMap k l = PPMap $ Map.fromList $ map (\v -> (v , createTable l)) (createTable k)

create1ConnPPMap :: Int -> Int -> PPMap
create1ConnPPMap m n = PPMap $ Map.fromList (map (\x -> (x , createTable n)) (create1ConnTable m))



-- Checking order between two elements of a poset
below , above :: Vert -> Vert -> Bool
x `below` y = all (\(e , e') -> toBool e' --> toBool e) (zip x y)
x `above` y = y `below` x

-- Given a potential substitution, generate all possible substitutions from it
getPMaps :: PPMap -> [PMap]
getPMaps (PPMap sigma) = map (PMap . Map.fromList) (getPMaps' (Map.toList sigma))
  where
  getPMaps' :: [(Vert , [Vert])] -> [[(Vert , Vert)]]
  getPMaps' [] = [[]]
  getPMaps' ((x , vs) : ys) = [ (x , v) : r | v <- vs , r <- getPMaps' (filterRec x v ys) ]

  filterRec :: Vert -> Vert -> [(Vert , [Vert])] -> [(Vert , [Vert])]
  filterRec x v = map (\(y, us) -> (y , [ u | u <- us , (y `below` x) --> (u `below` v) ]))

-- combinePMaps :: [PMap] -> PPMap
-- combinePMaps ss = Map.mapWithKey (\x _ -> nub (map (! x) ss)) (head ss)

-- Given a potential substitution, generate the substitution from it
-- (equivalent to head of getPMaps, but perhaps more efficient)
fstPMap :: PPMap -> PMap
fstPMap = PMap . Map.fromList . fstPPMap' . Map.toList . ppmap
  where
  fstPPMap' :: [(Vert , [Vert])] -> [(Vert , Vert)]
  fstPPMap' [] = []
  fstPPMap' ((x,vs) : yws) = (x , head vs) :
    fstPPMap' (map (\(y , ws) -> (y , filter (\w -> (y `below` x) --> (w `below` head vs)) ws)) yws)

updatePPMap :: PPMap -> Vert -> [Vert] -> PPMap
updatePPMap (PPMap sigma) x vs = PPMap $ Map.mapWithKey
  (\y us -> filter (\u ->
              (y `above` x) --> any (u `above`) vs &&
              (y `below` x) --> any (u `below`) vs
            ) us) (Map.insert x vs sigma)


