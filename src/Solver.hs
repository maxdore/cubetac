{-# LANGUAGE FlexibleContexts #-}

module Solver where

import Control.Applicative
import Control.Monad

import Prel
import Data
import Poset
import ContortionSolver
import CompositionSolver
import Formula
import Examples
import Data.List

import Debug.Trace

solve :: Cube -> Boundary -> Maybe Term
solve = solverec 0 5

solverec :: Int -> Int -> Cube -> Boundary -> Maybe Term
solverec depth mdepth ctxt goal =
  case findContortion ctxt goal of
    Just t -> Just t
    Nothing -> do
      if depth == mdepth
        then Nothing
        else do
          traceM $ "SOLVING (" ++ show depth ++ ") " ++ show goal
          res@(Comp (Box sts b)) <- findComposition ctxt goal

          traceM $ "FOUND " ++ show res ++ "\n : " ++ show (inferBoundary ctxt res)

          -- TODO ABSTRACT: give function that takes box with open faces and fills these faces
          -- TODO MAKE THIS SOME FOLD (UPDATE FACES ONE AFTER THE OTHER)
          -- TODO ALLOW FOR BACKTRACKING INSTEAD OF GIVING AN ERROR
          b' <- if b == Free
            then solverec (depth+1) mdepth ctxt (getBackBoundary ctxt (Box sts b))
            else return b
          let res' = Comp $ modifyBox (Box sts b') (\(i,e) t ->
                                                      if t == Free
                                                        then case solverec (depth+1) mdepth ctxt (getSideBoundary ctxt goal (Box sts b') (i,e)) of
                                                          Just t' -> t'
                                                          Nothing -> error "Free side could not be solved"
                                                        else t) id

          when (not (wellFormedBox ctxt (Box sts b)))
            (error $ "Solution is not a well-formed box")

          when (not (matchesBoundary ctxt res' goal))
            (error $ "Solution does not match goal:\n" ++ show res' ++ "\nhas boundary\n" ++ show (inferBoundary ctxt res'))

          when (depth == 0) (traceM (agdaShow res'))
          return res'




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
