{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Rulesets.Disj where

import Data.List
import Data.Maybe
import Control.Monad
import qualified Data.Map as Map

import Prel
import Core
import Poset

data Formula = Clause [IVar] | Endp Endpoint
  deriving (Eq, Show)

mapClause :: ([IVar] -> Formula) -> Formula -> Formula
mapClause f (Clause is) = f is
mapClause _ (Endp e) = Endp e

mapAtoms :: (IVar -> IVar) -> Formula -> Formula
mapAtoms f (Clause is) = Clause (map f is)
mapAtoms _ (Endp e) = Endp e

offset :: IVar -> [Formula] -> [Formula]
offset i = map (mapAtoms (\j -> if j < i then j else j-1))

subst :: Formula -> IVar -> Formula -> Formula
subst (Endp e) _ _ = Endp e
subst (Clause s) i (Clause t) | i `elem` s = Clause $ sort $ delete i s ++ t
                              | otherwise = Clause s


newtype Disj = Disj { rmdisj :: (IVar , [Formula])}
  deriving (Eq, Show)

disj2subst :: Disj -> PMap
disj2subst (Disj (m , rs)) = PMap $ Map.fromList (map (\v -> (v , (map (evalFormula v) rs))) (create1ConnTable m))
  where
  evalFormula :: Vert -> Formula -> Endpoint
  evalFormula _ (Endp e) = e
  evalFormula x (Clause is) = case elemIndex I1 x of
    Just i -> fromBool (i+1 `elem` is)
    Nothing -> I0

subst2disj :: PMap -> Disj
subst2disj (PMap sigma) = Disj (dom, map reconstrForm [1..cod])
  where
  dom = domdim (PMap sigma)
  cod = coddim (PMap sigma)
  reconstrForm :: IVar -> Formula
  reconstrForm i | (fromJust (Map.lookup ((replicate (dom) I0)) sigma))!!(i-1) == I1 = Endp I1
                 | otherwise = Clause [ j | j <- [1..dom] , (fromJust (Map.lookup (baseVert (dom) j) sigma))!!(i-1) == I1 ]


instance Bs Disj where
  tdim (Disj (m , _)) = m
  face (Disj (m , rs)) (i,e) =
    let rs' = if e == I0
                    then (map (mapClause (\(is) -> let is' = delete i is in if null is' then Endp I0 else Clause is'))) rs
                    else (map (mapClause (\(is) -> if i `elem` is then Endp I1 else Clause is ))) rs
    in Disj (m-1, offset i rs')
  deg d i = Disj (d+1 , [ Clause [j] | j <- [1..d+1] , j /= i])
  compose (Disj (m , ss)) (Disj (n , rs)) =
    let rs' = map (mapAtoms (\i -> i + m)) rs in
    let ss' = map (\d -> foldr (\i d' -> subst d' i (rs'!!(i-1))) d [1..n]) ss in
    ((Disj (n , map (mapAtoms (\i -> i - m)) ss')))

  isId (Disj (m , rs)) = rs == [Clause [i] | i <- [1..m]]
  isFace (Disj (_ , rs)) = case elemIndex (Endp I0) rs of
    Just i -> Just (i+1,I0)
    Nothing -> case elemIndex (Endp I1) rs of
      Just i -> Just (i+1,I1)
      Nothing -> Nothing
  rmI (Disj (m , rs)) i = Disj (m , take (i-1) rs ++ drop i rs)
  allConts m n = map (\rs -> Disj (m , rs)) (map (map Clause) (replicateM n (ps [1..m])))
  -- map subst2disj (getPMaps (Map.fromList $ map (\v -> (v , createPoset n)) (create1ConnPoset m)))

instance Rs Disj PPMap where
  allPConts _ m n = [ create1ConnPPMap m n ]
  unfold = (map subst2disj) . getPMaps
  combine = PPMap . combineMaps . (map (pmap . disj2subst))

  -- constrCont c gty (p , pty) = do
  --   traceM ("TRY TO CONTORT " ++ p)
  --   sigma <- foldM
  --                 (\sigma (ie , gf) -> do
  --                   traceM $ show ie ++ " : " ++ show sigma ++ " WITH " ++ show gf
  --                   theta <- case gf of
  --                       App (Var q) rs | q == p -> Just $ injPPMap (form2subst (rmdisj rs))
  --                       _ -> do
  --                         let theta = filter (\s -> traceShow s $ normalise c (App (Var p) (Disj (subst2form s))) == gf)
  --                                     (getPMaps (restrPPMap sigma ie))
  --                         traceShowM theta
  --                         if null theta
  --                           then Nothing
  --                           else Just (combinePMaps theta)
  --                   traceShowM theta
  --                   let theta' = foldl (\s x -> updatePPMap s (insInd ie x) (theta ! x)) sigma [ baseVert (tyDim gty-1) i | i <- [1..tyDim gty-1] ]
  --                   traceShowM theta'
  --                   return $ theta'
  --                     )
  --                 (create1ConnPPMap (tyDim gty) (tyDim pty))
  --                 (reverse (sortBy (\(_, s) (_,t) -> compare (baseDim c t) (baseDim c s))
  --                   [ (ie , getFace gty ie) | ie <- restrictions (tyDim gty) , sideSpec gty ie]
  --                 ))

  --   traceShowM (length (getPMaps sigma))
  --   return (App (Var p) (Disj (subst2form (fstPMap sigma))))
    -- Nothing




newtype Conj = Conj { rmconj :: (IVar , [Formula])}
  deriving (Eq, Show)


conj2subst :: Conj -> PMap
conj2subst (Conj (m , rs)) = PMap $ Map.fromList (map (\v -> (v , (map (evalFormula v) rs))) (create1ConnTable m))
  where
  evalFormula :: Vert -> Formula -> Endpoint
  evalFormula _ (Endp e) = e
  evalFormula x (Clause is) = case elemIndex I1 x of
    Just i -> fromBool (i+1 `elem` is || null is)
    Nothing -> fromBool (null is)

subst2conj :: PMap -> Conj
subst2conj (PMap sigma) = Conj (dom, map reconstrForm [1..cod])
  where
  dom = domdim (PMap sigma)
  cod = coddim (PMap sigma)
  reconstrForm :: IVar -> Formula
  reconstrForm i | (fromJust (Map.lookup ((replicate (dom) I0)) sigma))!!(i-1) == I1 = Clause []
                 | and (Map.map (\y -> (y)!!(i-1) == I0) sigma) = Endp I0
                 | otherwise = Clause [ j | j <- [1..dom] , (fromJust (Map.lookup (baseVert (dom) j) sigma))!!(i-1) == I1 ]




instance Bs Conj where
  tdim (Conj (m , _)) = m
  face (Conj (m , rs)) (i,e) =
    let rs' = if e == I0
                  then (map (mapClause (\is -> if i `elem` is then Endp I0 else Clause is))) rs
                  else (map (mapClause (\is -> let is' = delete i is in if null is' then Endp I1 else Clause is'))) rs
    in Conj (m-1, offset i rs')
  deg d i = Conj (d+1 , [ Clause [j] | j <- [1..d+1] , j /= i])
  compose (Conj (m , ss)) (Conj (n , rs)) =
    let rs' = map (mapAtoms (\i -> i + m)) rs in
    let ss' = map (\d -> foldr (\i d' -> subst d' i (rs'!!(i-1))) d [1..n]) ss in
    ((Conj (n , map (mapAtoms (\i -> i - m)) ss')))
  isId (Conj (m , rs)) = rs == [Clause [i] | i <- [1..m]]
  isFace (Conj (_ , rs)) = case elemIndex (Endp I0) rs of
    Just i -> Just (i+1,I0)
    Nothing -> case elemIndex (Endp I1) rs of
      Just i -> Just (i+1,I1)
      Nothing -> Nothing
  rmI (Conj (m , rs)) i = Conj (m , take (i-1) rs ++ drop i rs)
  allConts m n = map (\rs -> Conj (m , rs)) (map (map Clause) (replicateM n (ps [1..m])))

    -- map subst2conj (getPMaps (Map.fromList $ map (\v -> (v , createPoset n)) (create1ConnPoset m)))

instance Rs Conj PPMap where
  allPConts _ m n = [ create1ConnPPMap m n ]
  unfold = (map subst2conj) . getPMaps
  combine = PPMap . combineMaps . (map (pmap . conj2subst))
