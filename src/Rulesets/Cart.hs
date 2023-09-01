{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Rulesets.Cart where

import Data.List
import Control.Monad
import Prel
import Core

import Debug.Trace


data Formula = Atom IVar | Endpoint Endpoint
  deriving (Eq, Show)

mapAtom :: (IVar -> IVar) -> Formula  -> Formula
mapAtom f (Atom i) = Atom (f i)
mapAtom _ (Endpoint e) = Endpoint e

offset :: IVar -> [Formula] -> [Formula]
offset i = map (mapAtom (\j -> if j < i then j else j-1))

subst :: Formula -> IVar -> Formula -> Formula
subst (Atom s) i t | i == s = t
                   | otherwise = Atom s

allFormulas :: Dim -> Dim -> [[Formula]]
allFormulas n m = replicateM n [ Atom i | i <- [1..m]]

newtype Cart = Cart (IVar , [Formula])
  deriving (Eq, Show)

evalCart :: Cart -> IVar -> Endpoint -> Cart
evalCart (Cart (m , rs)) i e =
  let rs' = map (\(Atom j) -> if i == j then Endpoint e else Atom j) rs in
  Cart (m-1, offset i rs')

instance Bs Cart where
  tdim (Cart (m , _)) = m

  face (Cart (m , rs)) (i,e) =
    let rs' = map (\(Atom j) -> if i == j then Endpoint e else Atom j) rs in
    Cart (m-1, offset i rs')

  deg d i = Cart (d+1 , [ Atom j | j <- [1..d+1] , j /= i])

  compose (Cart (m , ss)) (Cart (n , rs)) =
    let rs' = map (mapAtom (\i -> i + m)) rs in
    let ss' = map (\d -> foldr (\i d' -> subst d' i (rs'!!(i-1))) d [1..n]) ss in
    (Cart (n , map (mapAtom (\i -> i - m)) ss'))

  isId (Cart (m , rs)) = rs == [Atom i | i <- [1..m]]

  isFace (Cart (m , rs)) = case elemIndex (Endpoint I0) rs of
    Just i -> Just (i+1,I0)
    Nothing -> case elemIndex (Endpoint I1) rs of
      Just i -> Just (i+1,I1)
      Nothing -> Nothing

  rmI (Cart (m , rs)) i = Cart (m , take (i-1) rs ++ drop i rs)

  allTerms c d = [ App (Var p) (Cart (d, r)) | (p,_) <- c , r <- allFormulas (idDim c p) d ]

