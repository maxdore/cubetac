module Prel where

import Data.List
import Data.Ord
import Control.Monad


x --> y   = not x || y



-- A function has a domain and codomain
-- (will be used for substitutions and potential substitutions)
class Fct a where
  domdim :: a -> Int
  coddim :: a -> Int

log2 :: Int -> Int
log2 1 = 0
log2 n = 1 + log2 (n `div` 2)

concatM :: (Monad m) => [a -> m a] -> (a -> m a)
concatM fs = foldr (>=>) return fs

ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM b t f = do b <- b; if b then t else f

whenM :: Monad m => m Bool -> m () -> m ()
whenM mb thing = do { b <- mb
                    ; when b thing }

andM :: Monad m => m Bool -> m Bool -> m Bool
andM mx my = do
  x <- mx
  if x
    then my
    else return x

ps :: [a] -> [[a]]
ps = filterM (const [True, False])

neps :: [a] -> [[a]]
neps xs = filter (not . null) (ps xs)

incps :: [a] -> [[a]]
incps = sortBy (comparing length) . ps

-- Order of filling does not matter anymore with filler CSP
-- psord :: [a] -> [[a]]
-- psord = concat . map permutations . ps

-- incpsbound :: Int -> [a] -> [[a]]
-- incpsbound d = (filter (\s -> length s <= d)) . incps

-- incpsord :: [a] -> [[a]]
-- incpsord = sortBy (comparing length) . psord

-- incpsordbound :: Int -> [a] -> [[a]]
-- incpsordbound d = (filter (\s -> length s <= d)) . incpsord

