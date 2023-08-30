{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Rulesets.Disj where

import Data.List
import Control.Monad
import Prel
import Core

import Debug.Trace


type Formula = [[IVar]]

offset :: IVar -> Formula -> Formula
offset i = map (map (\j -> if j < i then j else j-1))

subst :: [IVar] -> IVar -> [IVar] -> [IVar]
subst c i d | i `elem` c = sort $ delete i c ++ d
            | otherwise  = c

allFormulas :: Dim -> Dim -> [Formula]
allFormulas n m = replicateM n (neps [1..m])


newtype Disj = Disj (IVar , Formula)
  deriving (Eq, Show)

evalDisj :: Disj -> IVar -> Endpoint -> Disj
evalDisj (Disj (m , rs)) i e =
  let rs' = if e == I0
      then (map (delete i)) rs
      else map (\r -> if i `elem` r then [] else r) rs in
  Disj (m-1, offset i rs')

instance Rs Disj Disj where
  infer c t (Disj (m , r)) =
    Ty m [ (i,e) +> normalise c (App t (evalDisj (Disj (m , r)) i e)) | i <- [1..m] , e <- [I0,I1] ]

  normalise c (App (App t (Disj (m , ss))) (Disj (n , rs))) =
    let rs' = map (map (\i -> i + m)) rs in
    let ss' = map (\d -> foldr (\i d' -> subst d' i (rs'!!(i-1))) d [1..n]) ss in
    normalise c (App t (Disj (n , map (map (\i -> i - m)) ss')))
  normalise c (App (Var p) (Disj (m , rs))) | idDim c p == m && rs == [ [i] | i <- [1..length rs] ] =
      Var p
  normalise c (App t (Disj (m , rs))) =
      case findIndex null rs of
        Just i -> normalise c (App (getFace (inferTy c t) (i+1,I0)) (Disj (m , take i rs ++ drop (i+1) rs)))
        Nothing -> App t (Disj (m , filter (\d -> not (any (\d' -> d /= d' && intersect d d' == d) rs)) rs))

  allPTerms c d = [ App (Var p) (Disj (d, r)) | (p,_) <- c , r <- allFormulas (idDim c p) d ]

  deg c t i = let Ty d _ = inferTy c t in
    App t (Disj (d+1 , [ [j] | j <- [1..d+1] , j /= i]))

  unfold = singleton
  combine = head


newtype Conj = Conj (IVar , Formula)
  deriving (Eq, Show)

evalConj :: Conj -> IVar -> Endpoint -> Conj
evalConj (Conj (m , rs)) i e =
  let rs' = if e == I0
      then map (\r -> if i `elem` r then [] else r) rs
      else (map (delete i)) rs in
  Conj (m-1, offset i rs')

instance Rs Conj Conj where
  infer c t (Conj (m , r)) =
    Ty m [ (i,e) +> normalise c (App t (evalConj (Conj (m , r)) i e)) | i <- [1..m] , e <- [I0,I1] ]

  normalise c (App (App t (Conj (m , ss))) (Conj (n , rs))) =
    let rs' = map (map (\i -> i + m)) rs in
    let ss' = map (\d -> foldr (\i d' -> subst d' i (rs'!!(i-1))) d [1..n]) ss in
    normalise c (App t (Conj (n , map (map (\i -> i - m)) ss')))
  normalise c (App (Var p) (Conj (m , rs))) | idDim c p == m && rs == [ [i] | i <- [1..length rs] ] =
      Var p
  normalise c (App t (Conj (m , rs))) =
      case findIndex null rs of
        Just i -> normalise c (App (getFace (inferTy c t) (i+1,I0)) (Conj (m , take i rs ++ drop (i+1) rs)))
        Nothing -> App t (Conj (m , filter (\d -> not (any (\d' -> d /= d' && intersect d d' == d) rs)) rs))

  allPTerms c d = [ App (Var p) (Conj (d, r)) | (p,_) <- c , r <- allFormulas (idDim c p) d ]

  deg c t i = let Ty d _ = inferTy c t in
    App t (Conj (d+1 , [ [j] | j <- [1..d+1] , j /= i]))

  unfold = singleton
  combine = head


