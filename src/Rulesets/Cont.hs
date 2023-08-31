{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Rulesets.Cont where

import qualified Data.Map as Map

import Prel
import Core
import Poset

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
  deg d i = Map.fromList (map (\x -> (insInd i I0 x,x) ) (createPoset d)
                       ++ map (\x -> (insInd i I1 x,x) ) (createPoset d))
  compose = Map.compose
  isId = all (\(x,y) -> x == y) . Map.toList
  isFace = isSubposet . Map.elems
  rmI sigma i = Map.map (`removeInd` i) sigma


instance Rs Cont PCont where
  allPTerms c d = [ PApp (Var p) (createPSubst d d') | (p , Ty d' _) <- c ]
  unfold = getSubsts
  combine = combineSubsts
