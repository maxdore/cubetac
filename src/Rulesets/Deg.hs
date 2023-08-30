{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Rulesets.Deg where

import Data.List
import Core

-- data Deg = IVar
--   deriving (Eq, Show)
type Deg = IVar

allVarDeg :: Ctxt Deg Deg -> Id -> Dim -> [Term Deg Deg]
allVarDeg c p d | idDim c p > d = []
                | idDim c p == d-1 = [App (Var p) i | i <- [1..d] ]
                | otherwise =
                      nubBy (\t t' -> inferTy c t == inferTy c t')
                      [ deg c t j | t <- allVarDeg c p (d-1) , j <- [1..d] ]

instance Rs Deg Deg where
  infer c t i = let Ty n _ = inferTy c t in
    Ty (n+1) ([ (i,e) +> t | e <- [I0,I1] ]
          ++ [ ((if j < i then j else j+1),e) +> (App (termFace c t (j,e)) j) | j <- [1..n] , e <- [I0,I1] ])

  allPTerms c d = concat [ allVarDeg c p d | (p,_) <- c ]

  deg c t i = App t i

  unfold = singleton

  combine = head
