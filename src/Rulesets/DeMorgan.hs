{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Rulesets.DeMorgan where

import qualified Data.Map as Map
import Data.List
import Control.Monad

import Prel
import Core

import Debug.Trace

-- We save formulas as tuples of conjunctions of disjunctions, and we also have
-- to keep track of which variables we could use
data Atom = Pos IVar | Neg IVar
  deriving (Show, Ord, Eq)

a2i :: Atom -> IVar
a2i (Pos i) = i
a2i (Neg i) = i

mapAtom :: Atom -> (IVar -> IVar) -> Atom
mapAtom (Pos i) f = Pos (f i)
mapAtom (Neg i) f = Neg (f i)

type DMFormula = (IVar , [[[Atom]]])


offset :: IVar -> [[[Atom]]] -> [[[Atom]]]
offset i = map (map (map (\j -> if a2i j < i then j else mapAtom j (\a -> a - 1))))

eval :: DMFormula -> IVar -> Endpoint -> DMFormula
eval (m , rs) i e =
  let rs' = if e == I0
      then map (map (delete (Neg i))) (map (filter (Pos i `notElem`)) rs)
      else map (map (delete (Pos i))) (map (filter (Neg i `notElem`)) rs) in
  (m-1, offset i rs')

redDnf :: [[Atom]] -> [[Atom]]
redDnf r =
  let r' = map (nubBy (\d d' -> a2i d == a2i d')) r in
  filter (\d -> not (any (\d' -> d /= d' && intersect d d' == d) r')) r'

inDnf :: [[Atom]] -> Bool
inDnf phi = all (\c -> all (\d -> c == d || c \\ d /= []) phi) phi

allForm :: Dim -> Dim -> [DMFormula]
allForm m n = map (\rs -> (m , rs) ) (replicateM n rss)
  where
    subsets :: [IVar] -> [[Atom]]
    subsets [ i ] = [[ Pos i ] , [Neg i]]
    subsets (i : is) = let r = subsets is in
      [[Pos i] , [Neg i]] ++ r ++ map (Pos i:) r ++ map (Neg i:) r
    rss = filter inDnf (ps (subsets [1..m]))




instance Rs DMFormula DMFormula where
  infer c t (m , r) =
    Ty m [ (i,e) +> normalise c (App t (eval (m , r) i e)) | i <- [1..m] , e <- [I0,I1] ]

  normalise c (App (Var p) (m , rs))
    | idDim c p == m && rs == [ [[Pos i]] | i <- [1..length rs] ] =
      -- trace ("FOUND ID" ++ show (App (Var p) (m , rs))) $
      Var p
  normalise c (App t (m , rs)) | otherwise =
      -- trace ("NORM" ++ show (App t (m , rs))) $
        let ty = inferTy c t in
        case findIndex null rs of
          Just i -> normalise c (App (getFace ty (i+1,I0)) (m , take i rs ++ drop (i+1) rs))
          Nothing -> case findIndex ([] `elem`) rs of
            Just i -> normalise c (App (getFace ty (i+1,I1)) (m , take i rs ++ drop (i+1) rs))
            Nothing -> App t (m , map redDnf rs)


  allPTerms c d = [ PApp (Var p) rs | (p , Ty d' _) <- c , rs <- allForm d d' ]

  deg c t i = let Ty d _ = inferTy c t in
    App t (d+1 , [ [[Pos j]] | j <- [1..d+1] , j /= i])

  unfold = singleton
  combine = head



-- andOrp , idp , andp , idx :: Term DMFormula DMFormula
-- -- andOrp = App (Var "alpha") (3 , [[[1,2],[1,3]] , [[1],[2],[3]]])
-- andOrp = App (Var "p") (3 , [[[Pos 1, Neg 2],[Pos 1, Neg 3]]])
-- idp = App (Var "p") (0 , [[]])
-- andp = App (Var "p") (1 , [[[Pos 1]]])
-- idx = App (Var "x") (0 , [])
