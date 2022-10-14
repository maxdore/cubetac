{-# LANGUAGE FlexibleContexts #-}

module SimpleSolver where

import Control.Monad.Except
import Control.Monad.State
import Data.List
import Data.Map.Strict ((!), restrictKeys)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Prel
import Data
import Poset
import Solver



simpleSolve :: Id -> Solving s [Term]
simpleSolve f = do
  cube <- gets cube
  goal <- gets goal

  trace $ "TRY TO FIT " ++ f
  ty <- lookupDef f

  -- Create new constraint variable containing a single value: f matched to the goal
  cvar <- newCVar [createPTerm (Decl f ty) (dim goal)]

  mapM_ (\i -> do
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

