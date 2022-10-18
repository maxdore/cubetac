{-# LANGUAGE FlexibleContexts #-}

module SimpleSolver where

import Control.Monad.Except
import Control.Monad.State

import Prel
import Data
import Poset
import Solver


-- Given an identifier for a face in the context, try to stretch that face to
-- match the goal.
simpleSolve :: Id -> Solving s [Term]
simpleSolve f = do
  cube <- gets cube
  goal <- gets goal

  trace $ "TRY TO FIT " ++ f
  ty <- lookupDef f

  -- Create new constraint variable containing a single value: f matched to the goal
  cvar <- newCVar [createPTerm (Decl f ty) (dim goal)]

  -- For each dimension i from 0 to n-1, we check that the i-faces match the goal
  mapM_ (\i -> do

    -- Print the current potential substitution before matching the current dimension
    lookupDom cvar >>= trace . show
    trace ("MATCH DIM " ++ show i)

    mapM (\xs -> do
      a <- evalBoundary goal xs
      [sigma] <- lookupDom cvar
      res <- checkPTerm xs [a] sigma
      case res of
        Nothing -> guard False
        Just sigma' -> when (sigma /= sigma') (update cvar [sigma'])
        ) (getFaces (dim goal) i))
    [0..(dim goal - 1)]

  lookupDom cvar >>= trace . show
  res <- firstSubst cvar >>= \(PTerm _ sigma) -> return $ Term f (fstSubst sigma)
  lookupDom cvar >>= trace . show
  return [res]

