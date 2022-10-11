{-# LANGUAGE FlexibleContexts #-}

module SimpleSolver where

import Control.Monad.Except
import Control.Monad.State
import Data.List
import Data.Map ((!), Map)

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
  -- trace $ show i ++ "   " ++ show e
  let (a , b) = fgs !! (i - 1)
  let (Term f subst) = if e then b else a
  evalFace f (map (\x -> subst ! removeInd x i) xs)


checkPTerm :: [Vert] -> [Term] -> PTerm -> Solving s (Maybe PTerm)
checkPTerm xs as (PTerm f sigma) = do
  gads <-
    filterM (evalFace f >=> \b -> trace (show b) >> return (b `elem` as))
    (compGadgetImg (map (sigma !) xs))

  let vus = map (\i -> nub (map (!!i) gads)) [0 .. length xs - 1]
  return $ if any null vus
    then Nothing
    else Just $ PTerm f $ foldl (\s (x , vu) -> updatePSubst s x vu) sigma (zip xs vus)


simpleSolve :: Id -> Solving s [Term]
simpleSolve f = do
  cube <- gets cube
  goal <- gets goal

  trace "CUBE"
  mapM_ (trace . show) (constr cube)
  trace "GOAL"
  trace $ show goal

  trace $ "TRY TO FIT " ++ f

  ty <- lookupDef f

  cvar <- newCVar [createPTerm (Decl f ty) (dim goal)]

  mapM_ (\i -> do
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


  lookupDom cvar >>= \[PTerm _ sigma] -> (trace . show .subst2Tele . fstSubst) sigma

  -- res <- firstSubst cvar >>= \(PTerm id sigma) -> return $ Term id ((subst2Tele . fstSubst) sigma)
  -- return [res]

  return []
