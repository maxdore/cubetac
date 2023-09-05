{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Rulesets.Disj where

import Data.List
import Data.Maybe
import Control.Monad
import qualified Data.Map as Map
import Data.Map ((!), Map)

import Prel
import Core
import Poset

import Debug.Trace

data Formula = Clause [IVar] | Endpoint Endpoint
  deriving (Eq, Show)

mapAtoms :: (IVar -> IVar) -> Formula  -> Formula
mapAtoms f (Clause is) = Clause (map f is)
mapAtoms _ (Endpoint e) = Endpoint e

offset :: IVar -> [Formula] -> [Formula]
offset i = map (mapAtoms (\j -> if j < i then j else j-1))

subst :: Formula -> IVar -> Formula -> Formula
subst (Clause s) i (Clause t) | i `elem` s = Clause $ sort $ delete i s ++ t
                              | otherwise = Clause s

allFormulas :: Dim -> Dim -> [[Formula]]
allFormulas n m = map (map Clause) (replicateM n (neps [1..m]))


form2subst :: (IVar , [Formula]) -> Subst
form2subst (m , rs) = Map.fromList (map (\v -> (v , Vert (map (evalFormula v) rs))) (create1ConnPoset m))
  where
  evalFormula :: Vert -> Formula -> Endpoint
  evalFormula (Vert x) (Clause is) = case elemIndex I1 x of
    Just i -> fromBool (i+1 `elem` is)
    -- Nothing -> fromBool (null is)

subst2form :: Subst -> (IVar , [Formula])
subst2form sigma = (domdim sigma , map (\i ->
                            Clause [ j | j <- [1..domdim sigma] , toBools (fromJust (Map.lookup (baseVert (domdim sigma) j) sigma))!!(i-1) == I1 ]
                                                           ) [1..coddim sigma])


newtype Disj = Disj { rmdisj :: (IVar , [Formula])}
  deriving (Eq, Show)

instance Bs Disj where
  tdim (Disj (m , r)) = m
  face (Disj (m , rs)) (i,e) =
    let rs' = if e == I0
                    then (map (\(Clause is) -> let is' = delete i is in if null is' then Endpoint I0 else Clause is' )) rs
                    else (map (\(Clause is) -> if i `elem` is then Endpoint I1 else Clause is )) rs
    in Disj (m-1, offset i rs')
  deg d i = Disj (d+1 , [ Clause [j] | j <- [1..d+1] , j /= i])
  compose (Disj (m , ss)) (Disj (n , rs)) =
    let rs' = map (mapAtoms (\i -> i + m)) rs in
    let ss' = map (\d -> foldr (\i d' -> subst d' i (rs'!!(i-1))) d [1..n]) ss in
    ((Disj (n , map (mapAtoms (\i -> i - m)) ss')))

  isId (Disj (m , rs)) = rs == [Clause [i] | i <- [1..m]]
  isFace (Disj (m , rs)) = case elemIndex (Endpoint I0) rs of
    Just i -> Just (i+1,I0)
    Nothing -> case elemIndex (Endpoint I1) rs of
      Just i -> Just (i+1,I1)
      Nothing -> Nothing
  rmI (Disj (m , rs)) i = Disj (m , take (i-1) rs ++ drop i rs)
  allTerms c d = [ App (Var p) (Disj (d, r)) | (p,_) <- c , r <- allFormulas (idDim c p) d ]

instance Rs Disj PSubst where
  allPTerms c d = [ PApp (Var p) (Map.fromList $ map (\v -> (v , createPoset d')) (create1ConnPoset d)) | (p , Ty d' _) <- c ]
  unfold = (map (Disj . subst2form)) . getSubsts
  combine = combineSubsts . (map (form2subst . rmdisj))




newtype Conj = Conj { rmconj :: (IVar , [Formula])}
  deriving (Eq, Show)

instance Bs Conj where
  tdim (Conj (m , r)) = m
  face (Conj (m , rs)) (i,e) =
    let rs' = if e == I0
                  then (map (\(Clause is) -> if i `elem` is then Endpoint I0 else Clause is )) rs
                  else (map (\(Clause is) -> let is' = delete i is in if null is' then Endpoint I1 else Clause is' )) rs
    in Conj (m-1, offset i rs')
  deg d i = Conj (d+1 , [ Clause [j] | j <- [1..d+1] , j /= i])
  compose (Conj (m , ss)) (Conj (n , rs)) =
    let rs' = map (mapAtoms (\i -> i + m)) rs in
    let ss' = map (\d -> foldr (\i d' -> subst d' i (rs'!!(i-1))) d [1..n]) ss in
    ((Conj (n , map (mapAtoms (\i -> i - m)) ss')))
  isId (Conj (m , rs)) = rs == [Clause [i] | i <- [1..m]]
  isFace (Conj (m , rs)) = case elemIndex (Endpoint I0) rs of
    Just i -> Just (i+1,I0)
    Nothing -> case elemIndex (Endpoint I1) rs of
      Just i -> Just (i+1,I1)
      Nothing -> Nothing
  rmI (Conj (m , rs)) i = Conj (m , take (i-1) rs ++ drop i rs)
  allTerms c d = [ App (Var p) (Conj (d, r)) | (p,_) <- c , r <- allFormulas (idDim c p) d ]

instance Rs Conj PSubst where
  allPTerms c d = [ PApp (Var p) (Map.fromList $ map (\v -> (v , createPoset d')) (create1ConnPoset d)) | (p , Ty d' _) <- c ]
  unfold = (map (Conj . subst2form)) . getSubsts
  combine = combineSubsts . (map (form2subst . rmconj))

