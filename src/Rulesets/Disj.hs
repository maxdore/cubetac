{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Rulesets.Disj where

import Data.List
import Control.Monad
import Prel
import Core

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


newtype Disj = Disj (IVar , [Formula])
  deriving (Eq, Show)

evalDisj :: Disj -> IVar -> Endpoint -> Disj
evalDisj (Disj (m , rs)) i e =
  let rs' = if e == I0
      then (map (\(Clause is) -> let is' = delete i is in if is' == [] then Endpoint I0 else Clause is' )) rs
      else (map (\(Clause is) -> if i `elem` is then Endpoint I1 else Clause is )) rs
  in Disj (m-1, offset i rs')

instance Bs Disj where
  binfer c t (Disj (m , r)) =
    Ty m [ (i,e) +> bnormalise c (App t (evalDisj (Disj (m , r)) i e)) | i <- [1..m] , e <- [I0,I1] ]

  bnormalise c (App (App t (Disj (m , ss))) (Disj (n , rs))) =
    let rs' = map (mapAtoms (\i -> i + m)) rs in
    let ss' = map (\d -> foldr (\i d' -> subst d' i (rs'!!(i-1))) d [1..n]) ss in
    bnormalise c (App t (Disj (n , map (mapAtoms (\i -> i - m)) ss')))
  bnormalise c (App (Var p) (Disj (m , rs))) | idDim c p == m && rs == [ Clause [i] | i <- [1..length rs] ] =
      Var p
  bnormalise c (App t (Disj (m , rs))) =
      case elemIndex (Endpoint I0) rs of
        Just i -> bnormalise c (App (getFace (inferTy c t) (i+1,I0)) (Disj (m , take i rs ++ drop (i+1) rs)))
        Nothing -> case elemIndex (Endpoint I1) rs of
          Just i -> bnormalise c (App (getFace (inferTy c t) (i+1,I1)) (Disj (m , take i rs ++ drop (i+1) rs)))
          Nothing -> App t (Disj (m , rs))

  ballPTerms c d = [ App (Var p) (Disj (d, r)) | (p,_) <- c , r <- allFormulas (idDim c p) d ]

  bdeg c t i = let Ty d _ = inferTy c t in
    App t (Disj (d+1 , [ Clause [j] | j <- [1..d+1] , j /= i]))


newtype Conj = Conj (IVar , [Formula])
  deriving (Eq, Show)

evalConj :: Conj -> IVar -> Endpoint -> Conj
evalConj (Conj (m , rs)) i e =
  let rs' = if e == I0
      then (map (\(Clause is) -> if i `elem` is then Endpoint I0 else Clause is )) rs
      else (map (\(Clause is) -> let is' = delete i is in if is' == [] then Endpoint I1 else Clause is' )) rs
  in Conj (m-1, offset i rs')

instance Bs Conj where
  binfer c t (Conj (m , r)) =
    Ty m [ (i,e) +> bnormalise c (App t (evalConj (Conj (m , r)) i e)) | i <- [1..m] , e <- [I0,I1] ]

  bnormalise c (App (App t (Conj (m , ss))) (Conj (n , rs))) =
    let rs' = map (mapAtoms (\i -> i + m)) rs in
    let ss' = map (\d -> foldr (\i d' -> subst d' i (rs'!!(i-1))) d [1..n]) ss in
    bnormalise c (App t (Conj (n , map (mapAtoms (\i -> i - m)) ss')))
  bnormalise c (App (Var p) (Conj (m , rs))) | idDim c p == m && rs == [ Clause [i] | i <- [1..length rs] ] =
      Var p
  bnormalise c (App t (Conj (m , rs))) =
      case elemIndex (Endpoint I0) rs of
        Just i -> bnormalise c (App (getFace (inferTy c t) (i+1,I0)) (Conj (m , take i rs ++ drop (i+1) rs)))
        Nothing -> case elemIndex (Endpoint I1) rs of
          Just i -> bnormalise c (App (getFace (inferTy c t) (i+1,I1)) (Conj (m , take i rs ++ drop (i+1) rs)))
          Nothing -> App t (Conj (m , rs))

  ballPTerms c d = [ App (Var p) (Conj (d, r)) | (p,_) <- c , r <- allFormulas (idDim c p) d ]

  bdeg c t i = let Ty d _ = inferTy c t in
    App t (Conj (d+1 , [ Clause [j] | j <- [1..d+1] , j /= i]))


