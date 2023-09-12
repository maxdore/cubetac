{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Rulesets.PMap where

import qualified Data.Map as Map
import Data.Map ((!))
import Data.List
import Control.Monad

import Prel
import Core
import Poset

import Debug.Trace

isSubposet :: [Vert] -> Maybe Restr
isSubposet vs
  | null (head vs) = Nothing
  | all ((== I1) . head) vs = Just (1 , I1)
  | all ((== I0) . head) vs = Just (1 , I0)
  | otherwise = case isSubposet (map tail vs) of
      Nothing -> Nothing
      Just (i , e) -> Just (i + 1 , e)

instance Bs PMap where
  tdim sigma = domdim sigma
  face = restrPMap
  deg d i = Map.fromList (map (\x -> (insInd (i , I0) x , x) ) (createPoset d)
                       ++ map (\x -> (insInd (i , I1) x , x) ) (createPoset d))
  compose = Map.compose
  isId = all (\(x,y) -> x == y) . Map.toList
  isFace = isSubposet . Map.elems
  rmI sigma i = Map.map (`rmInd` i) sigma

instance Rs PMap PPMap where
  allPConts _ m n = [ createPPMap m n ]
  unfold = getPMaps
  combine = combinePMaps

  constrCont c gty (p , pty) = do
    sigma <- foldM
                  (\sigma (ie , gf) -> do
                    -- traceM $ show ie ++ " : " ++ show sigma ++ " : " ++ q ++ "<" ++ show tau ++ ">"
                    theta <- case gf of
                        App (Var q) tau | q == p -> Just $ injPPMap tau
                        _ -> do
                          let theta = filter (\s -> normalise c (App (Var p) s) == gf)
                                      (unfold (restrPPMap sigma ie))
                          if null theta
                            then Nothing
                            else Just (combine theta)
                    return $ foldl (\s x -> updatePPMap s (insInd ie x) (theta ! x)) sigma (createPoset (tyDim gty - 1))
                      )
                  (createPPMap (tyDim gty) (tyDim pty))
                  (sortBy (\(_, s) (_,t) -> compare (baseDim c t) (baseDim c s))
                    [ (ie , getFace gty ie) | ie <- restrictions (tyDim gty) , sideSpec gty ie])

    traceShowM (length (getPMaps sigma))
    return (App (Var p) (fstPMap sigma))
