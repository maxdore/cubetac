module Prel where

import Data.List


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
