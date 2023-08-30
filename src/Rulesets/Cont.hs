{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Rulesets.Cont where

import qualified Data.Map as Map
import Data.List
import Data.Maybe

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

isId :: Subst -> Bool
isId s = all (\(x,y) -> x == y) (Map.toList s)

restrSubst :: Subst -> Restr -> Subst
restrSubst sigma (i,e) = Map.mapKeys (`removeInd` i) (Map.filterWithKey (\x _ -> e == toBools x !! (i-1)) sigma)




-- createPContortion :: Decl -> Int -> PContortion
-- createPContortion (Decl f ty) gdim =
--   let img = createPoset (dim ty) in
--   let parts = map (\v -> (v , img)) (createPoset gdim) in
--   PContortion f (Map.fromList parts)


-- -- Given a potential substitution, restrict the values of x to vs
-- -- and make sure that the map is still a poset map
-- updatePSubst :: PSubst -> Vert -> [Vert] -> PSubst
-- updatePSubst sigma x vs = Map.mapWithKey (\y us -> filter (\u ->
--                                                         (y `above` x) --> any (u `above`) vs &&
--                                                         (y `below` x) --> any (u `below`) vs
--                                                       ) us) (Map.insert x vs sigma)

-- isEmptyPSubst :: PSubst -> Bool
-- isEmptyPSubst sigma = any (null . snd) (Map.toList sigma)


-- -- Given a pterm, what could its faces be?
-- possibleFaces :: Cube -> PContortion -> [Restr] -> [(Subst , Term)]
-- -- possibleFaces ctxt (PContortion p sigma) ies | trace ("myfun " ++ show (PContortion p sigma) ++ " " ++ show ies) False = undefined
-- possibleFaces ctxt (PContortion p sigma) ies = let ss = getSubsts sigma in
--   -- trace ("UNFOLDING " ++ show (length ss)) $
--   map (\s -> (s , termRestr ctxt (Term p s) ies)) ss

-- -- possibleFaces ctxt (Fixed t) ies = [(undefined , termRestr ctxt t ies)]


-- updateGadgets :: PSubst -> [Subst] -> [Restr] -> PSubst
-- updateGadgets sigma ss ies =
--   let xs = createPoset (domdim sigma) in
--   let vus = map (\x -> nub (map (! x) ss)) xs in -- TODO TAKE INTO ACCOUNT RESTRICTIONS!
--   foldl (\s (x , vu) -> updatePSubst s x vu) sigma (zip xs vus)

-- -- Given a pterm, filter it so that it some face of it is contained in a
-- -- collection of terms
-- filterPSubst :: Cube -> PContortion -> [Restr] -> [Term] -> Maybe PContortion
-- filterPSubst ctxt (PContortion p sigma) ies qs =
--   let ss = [ s | (s , q) <- possibleFaces ctxt (PContortion p sigma) ies , q `elem` qs ] in
--   let sigma' = updateGadgets sigma ss ies in
--   if isEmptyPSubst sigma'
--     then Nothing
--     else Just (PContortion p sigma')








type Cont = Subst
-- data Cont = Cont (Term Cont) Subst
--   deriving (Eq, Show)


type PCont = PSubst


instance Rs Cont PCont where
  infer c t s =
    let ty@(Ty n phi) = inferTy c t in
    let m = domdim s in
    let tup = [1..domdim s] :: [IVar] in
    Ty m [ (i,e) +> normalise c (App t (restrSubst s (i,e))) | i <- [1..m] , e <- [I0,I1]  ]

  normalise c (App ((App t tau)) sigma) = normalise c (App t (Map.compose tau sigma))
  normalise c (App t s) =
    if isId s
      then normalise c t
      else
        case isSubposet (Map.elems s) of
          Nothing -> App t s
          Just (i,e) ->
            -- TODO do we need to earlier capture in infer if the side is specified????
            let ty = inferTy c t in
            normalise c (App (getFace ty (i,e)) (Map.map (`removeInd` i) s))
  normalise c t = t


  allPTerms c d = [ PApp (Var p) (createPSubst d d') | (p , Ty d' _) <- c ]

  deg c t i = let Ty d _ = inferTy c t in
    App t (Map.fromList
                  (map (\x -> (insInd i I0 x,x) ) (createPoset d)
                    ++ map (\x -> (insInd i I1 x,x) ) (createPoset d)))

  unfold = getSubsts
  combine = combineSubsts


-- data PCont = PCont (Term Cont) PSubst
--   deriving (Eq, Show)

-- instance Wrapper PCont Cont where
--   unfold = getSubsts


