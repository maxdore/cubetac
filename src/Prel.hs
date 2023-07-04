module Prel where

import Data.List
import Control.Monad
import Data.Ord


x --> y   = not x || y



-- A function has a domain and codomain
-- (will be used for substitutions and potential substitutions)
class Fct a where
  domdim :: a -> Int
  coddim :: a -> Int



-- TODO better import from somewhere
anyM :: Monad m => (a -> m Bool) -> [a] -> m Bool
anyM f xs = go xs
  where
    go [] = return False
    go (x:xs) = do b <- f x
                   if b then return True
                        else go xs


log2 :: Int -> Int
log2 1 = 0
log2 n = 1 + log2 (n `div` 2)

splitOn :: (Char) -> String -> [String]
splitOn p s =  case dropWhile (==p) s of
                      "" -> []
                      s' -> w : splitOn p s''
                            where (w, s'') = break (==p) s'


splitAltern :: [a] -> ([a], [a])
splitAltern [] = ([], [])
splitAltern (x1:x2:xs) = (x1:odds, x2:evens)   
    where 
        (odds, evens) = splitAltern xs


indexOf :: (Eq a) => a -> [a] -> Int
indexOf n xs = go 0 n xs
    where
        go i n [] = (-1)
        go i n (x:xs)
             | n == x    = i
             | otherwise = go (i+1) n xs

foldM' :: (Monad m) => (a -> b -> m a) -> a -> [b] -> m a
foldM' _ z [] = return z
foldM' f z (x:xs) = do
  z' <- f z x
  z' `seq` foldM' f z' xs


incps :: [a] -> [[a]]
incps = (sortBy (comparing (length))) . (filterM (const [True, False]))
