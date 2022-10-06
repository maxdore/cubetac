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



-- filterPTerm1 :: [Vert] -> [Term] -> PTerm -> Solving s (Maybe PTerm)
-- filterPTerm1 [x , y] fs (PTerm f sigma) = do
--   fdim <- dimTerm f
--   case fdim of
--     0 -> if (emptT f `elem` fs) then return $ Just (PTerm f sigma) else return Nothing
--     _ -> do
--       let vs = sigma ! x
--       let us = sigma ! y

--       vs' <- filterM (\v -> anyM (\u -> evalEdge f v u >>= \g ->
--                                      case g of
--                                        Just g' -> return (g' `elem` fs)
--                                        Nothing -> return False
--                                      ) us) vs
--       us' <- filterM (\u -> anyM (\v -> evalEdge f v u >>= \g ->
--                                      case g of
--                                        Just g' -> return (g' `elem` fs)
--                                        Nothing -> return False
--                                      ) vs') us
--       if null vs' || null us'
--         then return Nothing
--         else do
--           let sigma' = Map.insert x vs' sigma
--           let sigma'' = Map.insert x vs' sigma'
--           let propagate = Map.mapWithKey (\z ws -> filter (\w ->
--                                                             (z `above` x) --> any (w `above`) vs' &&
--                                                             (z `below` x) --> any (w `below`) vs' &&
--                                                             (z `above` y) --> any (w `above`) us' &&
--                                                             (z `below` y) --> any (w `below`) us'
--                                                           ) ws) sigma''
--           return $ Just (PTerm f propagate)




-- evalFace :: Term -> Vert -> Solving s Term
-- evalFace (Term f s) x = do
--   goal <- gets goal
--   let sigma = tele2Subst s (dim goal - 1)
--   trace $ show sigma

--   return $ emptT "asd"

-- evalType :: Type -> Vert -> Solving s Term
-- evalType (Type ((a , b) : _)) (Vert (Endpoint e : es)) =
--   evalFace (if e then b else a) (Vert es)

-- evalType (Type [(Term a _ , Term b _)]) (Vert [Endpoint e]) = return $ Point (if e then b else a)
-- evalType (Type [(Term a _ , Term b _) , _]) (Vert [Endpoint e , Endpoint e']) =
--   evalPoint (if e then b else a) (Vert [Endpoint e'])
-- evalType (Type [(Term a _ , Term b _) , _ , _]) (Vert (Endpoint e : es)) =
--   evalPoint (if e then b else a) (Vert es)


-- evalType1 :: Type -> [Vert] -> Solving s Term
-- -- evalType1 (Type [(Term a _ , Term b _)]) (Vert [Endpoint e]) (Vert [Endpoint e]) = return $ Point (if e then b else a)
-- evalType1 (Type fs) [x , y] = do
--   let (i , Endpoint e) = getBoundary x y
--   trace $ show i ++ "|" ++ show e
--   let res = (if e then snd else fst) (fs !! (i - 1))
--   trace $ show res
--   return res


evalTerm :: Term -> [Vert] -> Solving s Term
evalTerm (Term id subst) [Vert es] = do
  let y = subst ! Vert es
  ty <- lookupDef id
  evalType ty [y]

evalType :: Type -> [Vert] -> Solving s Term
evalType (Type ((a , b) : _)) [Vert ((Endpoint e):es)] =
  evalTerm (if e then b else a) [Vert es]



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
  lookupDom cvar >>= trace . show

  mapM (\x -> do
    trace $ show x
    a <- evalType goal x
    trace $ show a
    -- addConstraint cvar $ do
    [sigma] <- lookupDom cvar
    return undefined
    -- res <- checkPTerm x [a] sigma
    -- case res of
    --   Nothing -> guard False
    --   Just sigma' -> when (sigma /= sigma') (update cvar [sigma'])
      ) (getFaces (dim goal) 0)

  trace "VERTICES MATCH"
  lookupDom cvar >>= trace . show

  -- -- when (dim goal > 1) (do
  -- mapM (\f -> do
  --           v <- evalType1 goal f
  --           -- addConstraint cvar $ do
  --           [sigma] <- lookupDom cvar
  --           res <- filterPTerm1 f [v] sigma
  --           trace $ show res
  --           case res of
  --             Nothing -> guard False
  --             Just sigma' -> update cvar [sigma']
  --       ) (getFaces (dim goal) 1)
  --                     -- )

  lookupDom cvar >>= trace . show

  -- res <- firstSubst cvar >>= \(PTerm id sigma) -> return $ Term id ((subst2Tele . fstSubst) sigma)
  -- return [res]

  return []
