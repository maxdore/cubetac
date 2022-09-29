module Poset where

import Data.List
import qualified Data.Map as Map
import Data.Map ((!), Map)

import Prel
import Data

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
  deriving (Eq , Ord )

instance Show Vert where
  show (Vert []) = ""
  show (Vert [e]) = show e
  show (Vert (e:es)) = show e ++ show (Vert es)


-- Construct an n-element poset
createPoset :: Int -> [Vert]
createPoset 0 = [Vert []]
createPoset n = let g = map toBools (createPoset (n - 1))
  in map (\v -> Vert (e0 : v)) g ++ map (\v -> Vert (e1 : v)) g

-- Predicates for checking relation between two elements of a poset
below , above :: Vert -> Vert -> Bool
x `below` y = all (\(e , e') -> toBool e' --> toBool e) (zip (toBools x) (toBools y))
x `above` y = y `below` x

-- Given two elements of a poset, compute the number of indices in which they differ
-- E.g., vdiff v u == 1 means that v and u are adjacent
vdiff :: Vert -> Vert -> Int
vdiff (Vert []) (Vert []) = 0
vdiff (Vert (e:es)) (Vert (e':es')) = (if e == e' then 0 else 1) + vdiff (Vert es) (Vert es')

-- If v and u have vdiff 1, then getPath yields the boundary prescribed by v and u,
-- E.g., i=1
getPath :: Vert -> Vert -> (Int , Endpoint)
getPath (Vert (e:es)) (Vert (e':es')) =
  if e == e'
    then (1 , e)
    else let (i , e'') = getPath (Vert es) (Vert es') in (i + 1 , e'')










