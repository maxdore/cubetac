module Deg where

import Data.List
import Core

data Deg = Deg (Term Deg) IVar
  deriving (Eq, Show)

allVarDeg :: Ctxt Deg -> Id -> Dim -> [Term Deg]
allVarDeg c p d | idDim c p > d = []
                | idDim c p == d-1 = [deg c (Var p) i | i <- [1..d] ]
                | otherwise =
                      nubBy (\t t' -> inferTy c t == inferTy c t')
                      [ deg c t j | t <- allVarDeg c p (d-1) , j <- [1..d] ]

instance Rs Deg where
  dim c (Deg t _) = 1 + termDim c t

  infer c (Deg t i) = let Ty n _ = inferTy c t in
    Ty (n+1) ([ (i,e) +> t | e <- [I0,I1] ]
          ++ [ ((if j < i then j else j+1),e) +> STerm (Deg (termFace c t (j,e)) j) | j <- [1..n] , e <- [I0,I1] ])

  allSTerms c d = concat [ allVarDeg c p d | (p,_) <- c ]

  deg c t i = STerm (Deg t i)



