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

insv :: Endpoint -> Vert -> Vert
e `insv` x = Vert (e: toBools x)

-- Construct an n-element poset
createPoset :: Int -> Poset
createPoset 0 = [Vert []]
createPoset n = let g = map toBools (createPoset (n - 1))
  in map (\v -> Vert (e0 : v)) g ++ map (\v -> Vert (e1 : v)) g

-- Given m and n, generate all n-dimensional faces of the m-element poset
getFaces :: Int -> Int -> [[Vert]]
getFaces m 0 = map (: []) (createPoset m)
getFaces m n | m == n = [ createPoset m ]
getFaces m n =
  map (map (e0 `insv`)) (getFaces (m-1) n)
  ++ map (map (e1 `insv`)) (getFaces (m-1) n)
  ++ map (\l -> map (e0 `insv`) l ++ map (e1 `insv`) l) (getFaces (m-1) (n-1))

-- Given two elements of a poset, compute the number of indices in which they differ
-- E.g., vdiff v u == 1 means that v and u are adjacent
vdiff :: Vert -> Vert -> Int
vdiff (Vert []) (Vert []) = 0
vdiff (Vert (e:es)) (Vert (e':es')) = (if e == e' then 0 else 1) + vdiff (Vert es) (Vert es')
vdiff _ _ = error "Comparing difference between elements of different posets"

-- Checking order between two elements of a poset
below , above , dirabove :: Vert -> Vert -> Bool
x `below` y = all (\(e , e') -> toBool e' --> toBool e) (zip (toBools x) (toBools y))
x `above` y = y `below` x
x `dirabove` y = x `above` y && vdiff x y == 1

-- Given a list of vertices, return the first index at which all vertices
-- have the same value, as well as that value
getFirstCommon :: [Vert] -> (Int , Endpoint)
getFirstCommon vs
  | all ((== e1) . head . toBools) vs = (1 , e1)
  | all ((== e0) . head . toBools) vs = (1 , e0)
  | otherwise = let (i , e) = getFirstCommon (map (Vert . tail . toBools) vs) in (i + 1 , e)

-- Given an element in a poset, remove the i-th index from it
removeInd :: Vert -> Int -> Vert
removeInd (Vert (_:es)) 1 = Vert es
removeInd (Vert (e:es)) n = Vert (e : toBools (removeInd (Vert es) (n-1)))
removeInd _ _ = error "This index is not part of the element"

insInd :: Int -> Endpoint -> Vert -> Vert
insInd i e (Vert es) = Vert (take (length es - i) es ++ [e] ++ drop (length es - i) es)

-- Given a list of n^2 elements of a poset, generate map from [1]^n to the elements
reconstrPMap :: [Vert] -> Map Vert Vert
reconstrPMap vs = Map.fromList (zip (createPoset (log2 (length vs))) vs)

