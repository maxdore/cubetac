module Prel where

import Data.List


x --> y   = not x || y

anyM :: Monad m => (a -> m Bool) -> [a] -> m Bool
anyM f xs = go xs
  where
    go [] = return False
    go (x:xs) = do b <- f x
                   if b then return True
                        else go xs

-- log2 :: Int -> Int
-- log2 1 = 0
-- log2 n = 1 + log2 (div n 2)
