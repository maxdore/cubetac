{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Rulesets.TruthTable where

import qualified Data.Map as Map
import Data.Map ((!))
import Data.List
import Control.Monad

import Prel
import Core
import Poset

import Debug.Trace

instance Bs TruthTable where
  tdim sigma = domdim sigma
  face (TruthTable sigma) r = TruthTable (restrMap sigma r)
  deg d i = TruthTable $ Map.fromList (map (\x -> (insInd (i , I0) x , x) ) (createTable d)
                       ++ map (\x -> (insInd (i , I1) x , x) ) (createTable d))
  compose (TruthTable sigma) (TruthTable tau) = TruthTable $ Map.compose sigma tau
  isId = all (\(x,y) -> x == y) . Map.toList . tt
  isFace = isFaceSet . Map.elems . tt
  rmI (TruthTable sigma) i = TruthTable $ Map.map (`rmInd` i) sigma

instance Rs TruthTable PTruthTable where
  allPConts _ m n = [ createPTruthTable m n ]
  unfold = getTruthTables
  combine = PTruthTable . combineMaps . (map tt)

  constrCont c gty (p , pty) = do
    sigma <- foldM
                  (\sigma (ie , gf) -> do
                    -- traceM $ show ie ++ " : " ++ show sigma ++ " : " ++ q ++ "<" ++ show tau ++ ">"
                    theta <- case gf of
                        App (Var q) tau | q == p -> (Just . PTruthTable . injPotMap . tt) tau
                        _ -> do
                          let theta = filter (\s -> normalise c (App (Var p) s) == gf)
                                      (unfold (PTruthTable (restrMap (ptt sigma) ie)))
                          if null theta
                            then Nothing
                            else Just (combine theta)
                    return $ foldl (\s x -> updatePTruthTable s (insInd ie x) ((ptt theta) ! x)) sigma (createTable (tyDim gty - 1))
                      )
                  (createPTruthTable (tyDim gty) (tyDim pty))
                  (sortBy (\(_, s) (_,t) -> compare (baseDim c t) (baseDim c s))
                    [ (ie , getFace gty ie) | ie <- restrictions (tyDim gty) , sideSpec gty ie])

    -- traceShowM (length (getPMaps sigma))
    let sols = (getTruthTables sigma) -- TODO filter
    return (App (Var p) (head sols))



  -- solve twop invGoal :: Term TruthTable PTruthTable
