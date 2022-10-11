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
import Formula



-- Construct a poset map from [0,1]
-- If face of something, evalFace to face

evalFace :: Id -> [Vert] -> Solving s Term
evalFace f vs = do
  ty <- lookupDef f
  case dim ty of
    0 -> return $ Term f (constSubst (log2 (length vs)))
    1 -> if any (\u -> head vs `vdiff` u > 0) (tail vs)
        then return $ Term f (reconstrPMap vs)
        else evalBoundary ty vs
    2 -> if any (\u -> head vs `vdiff` u > 1) (tail vs)
        then return $ Term f (reconstrPMap vs)
        else evalBoundary ty vs


evalBoundary :: Boundary -> [Vert] -> Solving s Term
evalBoundary (Boundary fgs) xs = do
  let (i , Endpoint e) = getFirstCommon xs
  let (a , b) = fgs !! (i - 1)
  let (Term f subst) = if e then b else a
  evalFace f (map (\x -> subst ! removeInd x i) xs)


checkPTerm :: [Vert] -> [Term] -> PTerm -> Solving s (Maybe PTerm)
checkPTerm xs as (PTerm f sigma) = do
  gads <-
    filterM (evalFace f >=> \b -> return (b `elem` as))
    (map (map snd . Map.toList) (getSubsts (sigma `restrictKeys` Set.fromList xs)))
  let vus = map (\i -> nub (map (!!i) gads)) [0 .. length xs - 1]
  return $ if any null vus
    then Nothing
    else Just $ PTerm f $ foldl (\s (x , vu) -> updatePSubst s x vu) sigma (zip xs vus)


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
    mapM (\x -> do
      a <- evalBoundary goal x
      [sigma] <- lookupDom cvar
      res <- checkPTerm x [a] sigma
      case res of
        Nothing -> guard False
        Just sigma' -> when (sigma /= sigma') (update cvar [sigma'])
        ) (getFaces (dim goal) i))
    [0..(dim goal - 1)]

  lookupDom cvar >>= trace . show
  res <- firstSubst cvar >>= \(PTerm f sigma) -> return $ Term f (fstSubst sigma)
  lookupDom cvar >>= trace . show
  return [res]

