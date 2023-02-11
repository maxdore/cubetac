{-# LANGUAGE FlexibleContexts, Strict #-}

module SimpleSolver where

import Data.List
import Data.Map.Strict (Map, (!), restrictKeys)
import qualified Data.Map.Strict as Map
import Control.Monad.State

import Prel
import Data
import Poset

import Debug.Trace




matchPSubst :: Cube -> Boundary -> Id -> [Subst]
matchPSubst ctxt goal p =
  let ty = lookupDef ctxt p in
  let psubst = foldr
                (\(i,e) sigma ->
                  let sigmaie = Map.mapKeys (`removeInd` (i+1)) (Map.filterWithKey (\x _ -> e == toBools x !! i) sigma) in
                  let ss = getSubsts sigmaie in
                  traceShow (length ss) $
                  let a = boundaryFace goal (i+1) e in
                  let ss' = filter (\s -> normalize ctxt (Term p s) == a) ss in
                  let xs = createPoset (dim goal - 1) in
                  let vus = map (\x -> nub (map (! x) ss')) xs in
                  foldl (\s (x , vu) -> updatePSubst s x vu) sigma (zip (map (insInd (dim goal - i) e) xs) vus)
                  )
                (createPSubst (dim goal) (dim ty))
                [ (i,e) | i <- [0..dim goal-1], e <- [e0,e1]] in

    traceShow psubst $
  let ss = getSubsts psubst in
  traceShow (length ss) $
  filter (\s -> inferBoundary ctxt (Term p s) == goal) ss



filterPSubst :: Cube -> Id -> PSubst -> Term -> PSubst
filterPSubst ctxt p sigma (Term q tau) = 
  -- trace ("FILTER " ++ show sigma ++ " MUST BE " ++ show (Term q tau)) $
  let ss = filter (\s -> normalize ctxt (Term p s) == Term q tau) (getSubsts sigma) in
  let xs = createPoset (domdim sigma) in
  let vus = map (\x -> nub (map (! x) ss)) xs in
  foldl (\s (x , vu) -> updatePSubst s x vu) sigma (zip xs vus)


matchDive :: Cube -> Term -> Id -> PSubst -> PSubst
matchDive ctxt (Term q tau) p sigma =
  if q == p
    then injPSubst tau
    else filterPSubst ctxt p sigma (Term q tau)


match :: Cube -> Boundary -> Id -> [Subst]
match ctxt goal p =
  -- traceShow ("MATCH " ++ show goal ++ " WITH " ++ p) $
  let faces = [ ((i,e) , boundaryFace goal (i+1) e) | i <- [0..dim goal-1], e <- [e1,e0]] in
  let ofaces = sortBy (\(_,Term r _) (_,Term s _) -> compare (tdim ctxt r) (tdim ctxt s)) faces in
  -- traceShow ofaces $
  let sigma = foldr
                (\((i,e) , t) sigma' ->
                    -- traceShow sigma' $
                    -- traceShow (i,e) $
                  let sigmaie = matchDive ctxt t p (restrPSubst sigma' i e) in
                  foldl (\s x -> updatePSubst s (insInd (dim goal - i - 1) e x) (sigmaie ! x)) sigma' (createPoset (dim goal - 1))
                  )
                (createPSubst (dim goal) (tdim ctxt p))
                ofaces in
  let ss = getSubsts sigma in
  let res = filter (\s -> inferBoundary ctxt (Term p s) == goal) ss in
  res





matchRecP :: Cube -> Boundary -> Id -> PSubst
matchRecP ctxt goal p = traceShow ("MATCH " ++ show goal ++ " WITH " ++ p) $
  if dim goal == 1
    then
      let ty = lookupDef ctxt p in
      let psubst = createPSubst (dim goal) (dim ty) in
        psubst
    else
      let ty = lookupDef ctxt p in
      let psubst = foldr
                    (\(i,e) sigma ->
                       -- traceShow (i,e) $
                       -- traceShow sigma $
                      let Term q tau = boundaryFace goal (i+1) e in
                      let sigmaie = (if q == p
                                  then injPSubst tau
                                  else matchRecP ctxt (inferBoundary ctxt (Term q tau)) p) in
                      let sigmaieunf = getSubsts sigmaie in
                        -- traceShow (length sigmaieunf) $
                      let ss = filter (\s -> normalize ctxt (Term p s) == Term q tau) sigmaieunf in
                      let xs = createPoset (dim goal - 1) in
                      let vus = map (\x -> nub (map (! x) ss)) xs in
                      foldl (\s (x , vu) -> updatePSubst s x vu) sigma (zip (map (insInd (dim goal - i) e) xs) vus)
                      )
                    (createPSubst (dim goal) (dim ty))
                    [ (i,e) | i <- [0..dim goal-1], e <- [e0,e1]] in
        psubst



-- [(000,[00]),(001,[01]),(100,[01]),(101,[11])]


matchRec :: Cube -> Boundary -> Id -> [Subst]
matchRec ctxt goal p =
  if dim goal == 1
    then
      let ty = lookupDef ctxt p in
      let psubst = createPSubst (dim goal) (dim ty) in
      filter (\s -> inferBoundary ctxt (Term p s) == goal) (getSubsts psubst)
    else
      let ty = lookupDef ctxt p in
      let psubst = foldr
                    (\(i,e) sigma ->
                      let Term q tau = boundaryFace goal (i+1) e in
                      let ss = (if q == p
                                  then [tau]
                                  -- else matchPSubst ctxt (inferBoundary ctxt (Term q tau)) p) in
                                  else matchRec ctxt (inferBoundary ctxt (Term q tau)) p) in
                      let xs = createPoset (dim goal - 1) in
                      let vus = map (\x -> nub (map (! x) ss)) xs in
                      let upd = zip (map (insInd (dim goal - i - 1) e) xs) vus in
                      foldl (\s (x , vu) -> updatePSubst s x (intersect (s!x) vu)) sigma upd
                      )
                    (createPSubst (dim goal) (dim ty))
                    [ (i,e) | i <- [0..dim goal-1], e <- [e0,e1]] in

      -- traceShow psubst $
      let ss = getSubsts psubst in
      -- traceShow (length ss) $
      let res = filter (\s -> inferBoundary ctxt (Term p s) == goal) ss in
      res


bruteForce :: Cube -> Boundary -> Id -> [Subst]
bruteForce ctxt goal p = 
  let ss = getSubsts (createPSubst (dim goal) (dim (lookupDef ctxt p))) in
    -- traceShow (length ss) $
  filter (\s -> inferBoundary ctxt (Term p s) == goal) ss


matchContortion :: Cube -> Boundary -> Id -> Maybe Term
matchContortion ctxt goal p =
  let substs = match ctxt goal p in
  if null substs
    then Nothing
    else Just $ Term p (head substs)

findContortion :: Cube -> Boundary -> Maybe Term
findContortion ctxt goal = msum (map (\(Decl id _) -> matchContortion ctxt goal id) (constr ctxt))



