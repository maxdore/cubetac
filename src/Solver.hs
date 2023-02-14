{-# LANGUAGE FlexibleContexts #-}

module Solver where

import Control.Applicative

import Prel
import Data
import Poset
import ContortionSolver
import CompositionSolver
import Formula
import Examples
import Data.List



solve :: Cube -> Boundary -> Maybe Term
solve ctxt goal = do
  res <- if containsBox goal
    then findComposition ctxt goal
    else findContortion ctxt goal <|> findComposition ctxt goal

  let resty = inferBoundary ctxt res
  if resty /= goal
    then error $ "Solution does not match goal:\n" ++ show res ++ "\nhas boundary\n" ++ show resty
    else return res




sg :: Ord a => [a] -> [[a]]
sg = group . sort

filterByLength :: Ord a => (Int -> Bool) -> [a] -> [[a]]
filterByLength p = filter (p . length) . sg

-- | 'repeated' finds only the elements that are present more than once in the list. Example:
--
-- > repeated  "foo bar" == "o"

repeated :: Ord a => [a] -> [a]
repeated = repeatedBy (>1)

-- | The repeatedBy function behaves just like repeated, except it uses a user-supplied equality predicate.
--
-- > repeatedBy (>2) "This is the test line" == " eist"

repeatedBy :: Ord a => (Int -> Bool) -> [a] -> [a]
repeatedBy p = map head . filterByLength p
