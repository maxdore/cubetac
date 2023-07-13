module Cont where

import qualified Data.Map as Map
import Data.Map ((!), Map)
import Data.List
import Core


newtype Vert = Vert { toBools :: [Endpoint]}
  deriving (Eq , Show, Ord)
type PSubst = Map Vert [Vert]

data Cont = Cont (Term Cont) PSubst
  deriving (Eq, Show)



instance Rs Cont where
  dim c (Cont t sigma) = undefined

  infer c (Cont t sigma) = undefined -- let Ty n _ = inferTy c t in
    -- Ty (n+1) ([ (i,e) +> t | e <- [I0,I1] ]
    --       ++ [ ((if j < i then j else j+1),e) +> STerm (MDeg (termFace c t (j,e)) j) | j <- [1..n] , e <- [I0,I1] ])

  allTerms c d = undefined




onep :: Ctxt Cont
onep = [
    ("x" , Ty 0 [])
  , ("y" , Ty 0 [])
  , ("p" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "y"])
      ]
