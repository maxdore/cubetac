module Prel where

import Data.List


x --> y   = not x || y



-- A function has a domain and codomain
-- (will be used for substitutions and potential substitutions)
class Fct a where
  domdim :: a -> Int
  coddim :: a -> Int

log2 :: Int -> Int
log2 1 = 0
log2 n = 1 + log2 (n `div` 2)

