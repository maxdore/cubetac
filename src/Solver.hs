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


solve :: Cube -> Boundary -> Maybe Term
solve ctxt goal = if containsBox goal
  then findComposition ctxt goal
  else findContortion ctxt goal <|> findComposition ctxt goal




