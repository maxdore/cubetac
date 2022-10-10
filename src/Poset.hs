module Poset where

import Data.List
import qualified Data.Map as Map
import Data.Map ((!), Map)

import Prel

-- Basic setup for posets

newtype Endpoint = Endpoint {toBool :: Bool}
  deriving (Eq , Ord)

instance Show Endpoint where
  show (Endpoint False) = "0"
  show (Endpoint True) = "1"

e0 , e1 :: Endpoint
e0 = Endpoint False
e1 = Endpoint True


-- An element of a poset is a list of 0s and 1s
newtype Vert = Vert { toBools :: [Endpoint]}
  deriving (Eq , Ord)

instance Show Vert where
  show (Vert []) = ""
  show (Vert [e]) = show e
  show (Vert (e:es)) = show e ++ show (Vert es)

type Poset = [Vert]

-- Construct an n-element poset
createPoset :: Int -> Poset
createPoset 0 = [Vert []]
createPoset n = let g = map toBools (createPoset (n - 1))
  in map (\v -> Vert (e0 : v)) g ++ map (\v -> Vert (e1 : v)) g

insv :: Endpoint -> Vert -> Vert
e `insv` x = Vert (e: toBools (x))


getFaces :: Int -> Int -> [[Vert]]
getFaces m 0 = map (\x -> [x]) (createPoset m)
getFaces m n | m == n = [ createPoset m ]
getFaces m n =
  map (map (e0 `insv`)) (getFaces (m-1) n)
  ++ map (map (e1 `insv`)) (getFaces (m-1) n)
  ++ map (\l -> map (e0 `insv`) l ++ map (e1 `insv`) l) (getFaces (m-1) (n-1))




-- Predicates for checking relation between two elements of a poset
below , above , dirabove :: Vert -> Vert -> Bool
x `below` y = all (\(e , e') -> toBool e' --> toBool e) (zip (toBools x) (toBools y))
x `above` y = y `below` x

x `dirabove` y = x `above` y && vdiff x y == 1

-- Given two elements of a poset, compute the number of indices in which they differ
-- E.g., vdiff v u == 1 means that v and u are adjacent
vdiff :: Vert -> Vert -> Int
vdiff (Vert []) (Vert []) = 0
vdiff (Vert (e:es)) (Vert (e':es')) = (if e == e' then 0 else 1) + vdiff (Vert es) (Vert es')

-- If v and u have vdiff 1, then getPath yields the boundary prescribed by v and u,
-- E.g., i=1
-- getBoundary :: Vert -> Vert -> (Int , Endpoint)
-- getBoundary (Vert (e:es)) (Vert (e':es')) =
--   if e == e'
--     then (1 , e)
--     else let (i , e'') = getBoundary (Vert es) (Vert es') in (i + 1 , e'')


getFirstCommon :: [Vert] -> (Int , Endpoint)
getFirstCommon vs =
  if (all (== True) (map (toBool . head . toBools) vs))
    then (1 , e1)
    else if (all (== False) (map (toBool . head . toBools) vs))
      then (1 , e0)
      else let (i , e'') = getFirstCommon (map (Vert . tail .toBools) vs) in (i + 1 , e'')



removeInd :: Vert -> Int -> Vert
removeInd (Vert (e:es)) 1 = Vert es
removeInd (Vert (e:es)) n = Vert (e : toBools (removeInd (Vert es) (n-1)))


-- A gadget is a (direct/correct/plain) n-face of a cube (vertices, lines with
-- length 1, diamonds with all edges length 1 etc)

-- Implicit that these are images of gadgets
compGadgetImg :: [[Vert]] -> [[Vert]]
compGadgetImg [vs] = map singleton vs
compGadgetImg [vs , us] = [ [v , u] | v <- vs , u <- us , v `above` u ]
compGadgetImg [vs , us , ts , ss] = [ [v , u , t , s ] | v <- vs , u <- us , v `above` u , t <- ts , v `above` t , s <- ss , u `above` s, t `above` s ]



reconstrPMap :: [Vert] -> Map Vert Vert
reconstrPMap vs = Map.fromList (zip (createPoset (log2 (length vs))) vs)


