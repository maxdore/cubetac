{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Rulesets.Cont where

import qualified Data.Map as Map
import Data.Map ((!), Map)
import Data.List
import Control.Monad
import Control.Monad.State

import Prel
import Core
import Poset

import Debug.Trace

isSubposet :: [Vert] -> Maybe Restr
isSubposet vs
  | null (toBools (head vs)) = Nothing
  | all ((== I1) . head . toBools) vs = Just (1 , I1)
  | all ((== I0) . head . toBools) vs = Just (1 , I0)
  | otherwise = case isSubposet (map (Vert . tail . toBools) vs) of
      Nothing -> Nothing
      Just (i , e) -> Just (i + 1 , e)

restrSubst :: Subst -> Restr -> Subst
restrSubst sigma (i,e) = Map.mapKeys (`removeInd` i) (Map.filterWithKey (\x _ -> e == toBools x !! (i-1)) sigma)

type Cont = Subst
type PCont = PSubst

instance Bs Cont where
  tdim sigma = domdim sigma
  face = restrSubst
  deg d i = Map.fromList (map (\x -> (insInd (i , I0) x,x) ) (createPoset d)
                       ++ map (\x -> (insInd (i , I1) x,x) ) (createPoset d))
  compose = Map.compose
  isId = all (\(x,y) -> x == y) . Map.toList
  isFace = isSubposet . Map.elems
  rmI sigma i = Map.map (`removeInd` i) sigma


instance Rs Cont PCont where
  allPConts _ m n = [ createPSubst m n ]
  unfold = getSubsts
  combine = combineSubsts

  constrCont c gty (p , pty) = do
    sigma <- foldM
                  (\sigma (ie , gf) -> do
                    -- traceM $ show ie ++ " : " ++ show sigma ++ " : " ++ q ++ "<" ++ show tau ++ ">"
                    theta <- case gf of
                        App (Var q) tau | q == p -> Just $ injPSubst tau
                        _ -> do
                          let theta = filter (\s -> normalise c (App (Var p) s) == gf)
                                      (unfold (restrPSubst sigma ie))
                          if null theta
                            then Nothing
                            else Just (combine theta)
                    return $ foldl (\s x -> updatePSubst s (insInd ie x) (theta ! x)) sigma (createPoset (tyDim gty - 1))
                      )
                  (createPSubst (tyDim gty) (tyDim pty))
                  (sortBy (\(_, s) (_,t) -> compare (baseDim c t) (baseDim c s))
                    [ (ie , getFace gty ie) | ie <- restrictions (tyDim gty) , sideSpec gty ie])

    traceShowM (length (getSubsts sigma))
    return (App (Var p) (fstSubst sigma))
