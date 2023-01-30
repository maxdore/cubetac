{-# LANGUAGE FlexibleContexts, Strict #-}

module ContortionSolver where

import Data.List
import Data.Map.Strict (Map, (!), restrictKeys)
import qualified Data.Map.Strict as Map
import Control.Monad.State

import Prel
import Poset
import Data

import Debug.Trace


findContortion :: Cube -> Boundary -> Maybe Term
findContortion ctxt goal = msum (map (\(Decl id _) -> match ctxt goal id) (constr ctxt))


match :: Cube -> Boundary -> Id -> Maybe Term
match ctxt goal p = do
  -- traceShowM ("MATCH " ++ show goal ++ " WITH " ++ p)
  let pdef = lookupDef ctxt p
  let faces = [ ((i,e) , boundaryFace goal (i+1) e) | i <- [0..dim goal-1], e <- [e1,e0]]
  let ofaces = sortBy (\(_,Term _ s) (_,Term _ t) -> compare (coddim t) (coddim s)) faces
  -- traceShowM ofaces
  sigma <- foldM
                (\sigma' ((i,e) , Term q tau)  -> do
                  traceShowM sigma'
                  traceShowM (i,e)
                  PTerm _ sigmaie <- if q == p
                      then Just $ PTerm p $ injPSubst tau
                      else filterPSubstGen ctxt (PTerm p (restrPSubst sigma' i e)) [] [Term q tau]
                  return $ foldl (\s x -> updatePSubst s (insInd (dim goal - i - 1) e x) (sigmaie ! x)) sigma' (createPoset (dim goal - 1))
                    )
                (createPSubst (dim goal) (dim pdef))
                ofaces

  let ss = getSubsts sigma
  traceM $ show (length ss) ++ " possible solutions found"
  let res = filter (\s -> inferBoundary ctxt (Term p s) == goal) ss  -- TODO FILTER NECESSARY?
  if null res
    then Nothing
    else Just $ Term p (head res)

bruteForce :: Cube -> Boundary -> Maybe Term
bruteForce ctxt goal = msum (map (\(Decl p  _) -> tryFace p) (constr ctxt))
  where
    tryFace p = 
        let ss = getSubsts (createPSubst (dim goal) (dim (lookupDef ctxt p))) in
          traceShow (length ss) $
        let res = filter (\s -> inferBoundary ctxt (Term p s) == goal) ss in
        if null res
          then Nothing
          else Just $ Term p (head res)

-- matchDive :: Cube -> Term -> PTerm -> Maybe PTerm
-- matchDive ctxt (Term q tau) (PTerm p sigma) =




-- recursive implementation would require following type
-- match :: Cube -> Boundary -> Id -> [Subst]


-- matchPSubst :: Cube -> Boundary -> Id -> [Subst]
-- matchPSubst ctxt goal p =
--   let ty = lookupDef ctxt p in
--   let psubst = foldr
--                 (\(i,e) sigma ->
--                   let sigmaie = Map.mapKeys (`removeInd` (i+1)) (Map.filterWithKey (\x _ -> e == toBools x !! i) sigma) in
--                   let ss = getSubsts sigmaie in
--                   traceShow (length ss) $
--                   let a = boundaryFace goal (i+1) e in
--                   let ss' = filter (\s -> normalize ctxt (Term p s) == a) ss in
--                   let xs = createPoset (dim goal - 1) in
--                   let vus = map (\x -> nub (map (! x) ss')) xs in
--                   foldl (\s (x , vu) -> updatePSubst s x vu) sigma (zip (map (insInd (dim goal - i) e) xs) vus)
--                   )
--                 (createPSubst (dim goal) (dim ty))
--                 [ (i,e) | i <- [0..dim goal-1], e <- [e0,e1]] in

--     traceShow psubst $
--   let ss = getSubsts psubst in
--   traceShow (length ss) $
--   filter (\s -> inferBoundary ctxt (Term p s) == goal) ss







-- matchRecP :: Cube -> Boundary -> Id -> PSubst
-- matchRecP ctxt goal p = traceShow ("MATCH " ++ show goal ++ " WITH " ++ p) $
--   if dim goal == 1
--     then
--       let ty = lookupDef ctxt p in
--       let psubst = createPSubst (dim goal) (dim ty) in
--         psubst
--     else
--       let ty = lookupDef ctxt p in
--       let psubst = foldr
--                     (\(i,e) sigma ->
--                        traceShow (i,e) $
--                        traceShow sigma $
--                       let Term q tau = boundaryFace goal (i+1) e in
--                       let sigmaie = (if q == p
--                                   then injPSubst tau
--                                   else matchRecP ctxt (inferBoundary ctxt (Term q tau)) p) in
--                       let sigmaieunf = getSubsts sigmaie in
--                         traceShow (length sigmaieunf) $
--                       let ss = filter (\s -> normalize ctxt (Term p s) == Term q tau) sigmaieunf in
--                       let xs = createPoset (dim goal - 1) in
--                       let vus = map (\x -> nub (map (! x) ss)) xs in
--                       foldl (\s (x , vu) -> updatePSubst s x vu) sigma (zip (map (insInd (dim goal - i) e) xs) vus)
--                       )
--                     (createPSubst (dim goal) (dim ty))
--                     [ (i,e) | i <- [0..dim goal-1], e <- [e0,e1]] in
--         psubst



-- -- [(000,[00]),(001,[01]),(100,[01]),(101,[11])]


-- matchRec :: Cube -> Boundary -> Id -> [Subst]
-- matchRec ctxt goal p =
--   if dim goal == 1
--     then
--       let ty = lookupDef ctxt p in
--       let psubst = createPSubst (dim goal) (dim ty) in
--       filter (\s -> inferBoundary ctxt (Term p s) == goal) (getSubsts psubst)
--     else
--       let ty = lookupDef ctxt p in
--       let psubst = foldr
--                     (\(i,e) sigma ->
--                       let Term q tau = boundaryFace goal (i+1) e in
--                       let ss = (if q == p
--                                   then [tau]
--                                   -- else matchPSubst ctxt (inferBoundary ctxt (Term q tau)) p) in
--                                   else matchRec ctxt (inferBoundary ctxt (Term q tau)) p) in
--                       let xs = createPoset (dim goal - 1) in
--                       let vus = map (\x -> nub (map (! x) ss)) xs in
--                       let upd = zip (map (insInd (dim goal - i - 1) e) xs) vus in
--                       foldl (\s (x , vu) -> updatePSubst s x ((s!x) `intersect` vu)) sigma upd
--                       )
--                     (createPSubst (dim goal) (dim ty))
--                     [ (i,e) | i <- [0..dim goal-1], e <- [e0,e1]] in

--       -- traceShow psubst $
--       let ss = getSubsts psubst in
--       traceShow (length ss) $
--       let res = filter (\s -> inferBoundary ctxt (Term p s) == goal) ss in
--       res




