{-# LANGUAGE FlexibleContexts #-}

module SimpleSolver where

import Control.Monad.Except
import Control.Monad.State
import Data.Maybe
import Data.List
import qualified Data.Map as Map
import Data.Map ((!), Map)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Either

import qualified Debug.Trace as D

import Prel
import Data
import Poset
import Solver
import Formula






-- Construct a poset map from [0,1]
-- If face of something, evalFace to face

evalFace :: Id -> [Vert] -> Solving s Term

evalFace id [v] = do
  ty <- lookupDef id
  case dim ty of
    0 -> return $ Term id (constSubst 0)
    _ -> evalBoundary ty [v]

evalFace id [v , u] = do
  ty <- lookupDef id
  case dim ty of
    0 -> return $ Term id (constSubst 1)
    1 -> return $ Term id idSubst
    2 -> do
      case v `vdiff` u of
        0 -> evalBoundary ty [v,u]
        1 -> evalBoundary ty [v,u]
        2 -> do
          -- trace "DIAGONAL"
          return $ Term id (reconstrPMap [v,u]) -- (Map.fromList [(Vert[e0],v),(Vert[e1],u)])

evalFace id [v , u , t , s] = do
  ty <- lookupDef id
  case dim ty of
    0 -> return $ Term id (constSubst 2)
    2 -> do
      trace $ show id ++ " @ " ++ show [v , u , t , s]
      return $ Term id (reconstrPMap [v,u,t,s])
      -- evalBoundary ty [v , u , t , s]





evalBoundary :: Boundary -> [Vert] -> Solving s Term
evalBoundary (Boundary abs) xs = do
  let (i , Endpoint e) = getFirstCommon xs
  -- trace $ show i ++ "   " ++ show e
  let (a , b) = abs !! (i - 1)
  let (Term id subst) = if e then b else a
  evalFace id (map (\x -> subst ! (removeInd x i)) xs)

-- evalTerm :: Term -> [Vert] -> Solving s Term
-- evalTerm (Term id subst) xs = evalFace id (map (subst !) xs)



-- This function modifies a psubst such that it assigns at vertex x only terms
-- which are in as
checkPTerm :: [Vert] -> [Term] -> PTerm -> Solving s (Maybe PTerm)
checkPTerm xs as (PTerm id sigma) = do
  gads <- filterM (\vu -> evalFace id vu >>= \b -> trace (show vu) >> return (b `elem` as)) (compGadgetImg (map (sigma !) xs))
  let vus = map (\i -> nub (map (!!i) gads)) [0 .. length xs - 1]
  if any null vus
    then return Nothing
    else return $ Just $ PTerm id $ foldl (\s (x , vu) -> updatePSubst s x vu) sigma (zip xs vus)
    -- map (\(x , vu) -> updatePSubst prevs x vu) (zip xs vus')
    -- (updatePSubst (updatePSubst sigma x vs) y us)

-- checkPTerm [x] as (PTerm id sigma) = do
--   -- ty <- lookupDef id
--   -- vs <- filterM (\v -> evalBoundary ty [v] >>= \b -> return (b `elem` as)) (sigma ! x)
--   vs <- filterM (\v -> evalFace id [v] >>= \b -> return (b `elem` as)) (sigma ! x)
--   trace $ show vs
--   if null vs
--     then return Nothing
--     else return $ Just (PTerm id (updatePSubst sigma x vs))

-- checkPTerm [x,y] as (PTerm id sigma) = do
--   vus <- filterM (\vu -> evalFace id vu >>= \b -> trace (show b) >> return (b `elem` as)) (compGadgetImg [sigma ! x , sigma ! y])
--   trace $ show vus
--   let vs = nub $ map (!!0) vus
--   let us = nub $ map (!!1) vus
--   trace $ "RESTRICT TO " ++ show vs ++ " ; " ++ show us
--   if null vs || null us
--     then return Nothing
--     else return $ Just (PTerm id (updatePSubst (updatePSubst sigma x vs) y us))

-- checkPTerm [x,y,z,w] as (PTerm id sigma) = do
--   -- ty <- lookupDef id
--   -- vus <- filterM (\vu -> evalBoundary ty vu >>= \b -> return (b `elem` as)) (compGadgetImg [sigma ! x , sigma ! y , sigma ! z , sigma ! w])
--   vus <- filterM (\vu -> evalFace id vu >>= \b -> return (b `elem` as)) (compGadgetImg [sigma ! x , sigma ! y , sigma ! z , sigma ! w])
--   trace $ show vus
--   let vs = nub $ map (!!0) vus
--   let us = nub $ map (!!1) vus
--   let ts = nub $ map (!!2) vus
--   let ss = nub $ map (!!3) vus
--   trace $ "RESTRICT TO " ++ show vs ++ " ; " ++ show us ++ " ; " ++ show ts ++ " ; " ++ show ss
--   if null vs || null us || null ts || null ss
--     then return Nothing
--     else return $ Just (PTerm id (updatePSubst (updatePSubst (updatePSubst (updatePSubst sigma x vs) y us) z ts) w ss))



simpleSolve :: Id -> Solving s [Term]
simpleSolve id = do
  cube <- gets cube
  goal <- gets goal

  trace "CUBE"
  mapM (trace . show) (constr cube)
  trace "GOAL"
  trace $ show goal

  trace $ "TRY TO FIT " ++ id 

  ty <- lookupDef id

  cvar <- newCVar [(createPTerm (Decl id ty) (dim goal))]

  mapM (\i -> do
    lookupDom cvar >>= trace . show
    trace ("MATCH DIM " ++ show i)
    mapM (\x -> do
      trace $ show x
      lookupDom cvar >>= trace . show
      a <- evalBoundary goal x
      trace $ "HAS TO BE " ++ show a
      -- addConstraint cvar $ do
      [sigma] <- lookupDom cvar
      res <- checkPTerm x [a] sigma
      case res of
        Nothing -> guard False
        Just sigma' -> when (sigma /= sigma') (update cvar [sigma'])
        ) (getFaces (dim goal) i))

    [0..(dim goal - 1)]


  lookupDom cvar >>= \[PTerm id sigma] -> (trace . show .subst2Tele . fstSubst) sigma

  -- res <- firstSubst cvar >>= \(PTerm id sigma) -> return $ Term id ((subst2Tele . fstSubst) sigma)
  -- return [res]

  return []
