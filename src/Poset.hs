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

inse :: Endpoint -> Vert -> Vert
e `inse` x = Vert (e: toBools (x))

-- createPos :: Int -> [[Endpoint]]
-- createPos 0 = [[]]
-- createPos n = let g = (createPos (n - 1))
--   in map (\v -> (e0 : v)) g ++ map (\v -> (e1 : v)) g

getFaces :: Int -> Int -> [[Vert]]
getFaces m 0 = map (\x -> [x]) (createPoset m)
getFaces m n | m == n = [ createPoset m ]
getFaces m n =
  map (map (e0 `inse`)) (getFaces (m-1) n)
  ++ map (map (Vert . (e1:) . toBools)) (getFaces (m-1) n)
  ++ map (\l -> map (Vert . (e0:) . toBools) l ++ map (Vert . (e1:) . toBools) l) (getFaces (m-1) (n-1))




-- The dimension of the poset and the dimension of the face
-- getFaces :: Int -> Int -> [[Vert]]
-- getFaces m n =
--   let flips = createPoset n in
--   let dims = [ (i , e) | i <- [1 .. m] , e <- [e0 , e1]]

--   map ($) [ map (\x -> vinsert x i e) flips | (i,e) <- dims , _ <- [1 .. m-n]]

--   map (\(i , e) ->)

--   where
--   vinsert :: Vert -> Int -> Endpoint -> Vert
--   vinsert (Vert xs) 1 e = Vert (e : xs)
--   vinsert (Vert (x : xs)) n e = Vert (x : toBools (vinsert (Vert xs) (n - 1) e))

-- getFaces xs 0 = map (\x -> [x]) xs
-- getFaces xs 1 = concat $ map (\x -> [ [x , y] | y <- xs, x `above` y , vdiff x y == 1 ]) xs
-- getFaces xs 2 = concat $ map (\x -> [ [x , y , z , w] | y <- xs, z <- xs , w <- xs ,
--                                       x `dirabove` y && x `dirabove` z &&
--                                       y `dirabove` w && z `dirabove` w
--                                                       ]) xs





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
getBoundary :: Vert -> Vert -> (Int , Endpoint)
getBoundary (Vert (e:es)) (Vert (e':es')) =
  if e == e'
    then (1 , e)
    else let (i , e'') = getBoundary (Vert es) (Vert es') in (i + 1 , e'')










