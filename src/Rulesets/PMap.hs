{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Rulesets.PMap where

import qualified Data.Map as Map
import Data.Map ((!))
import Data.List
import Control.Monad

import Prel
import Core
import Poset

import Debug.Trace


instance Bs PMap where
  tdim sigma = domdim sigma
  face (PMap sigma) r = PMap (restrMap sigma r)
  deg d i = PMap $ Map.fromList (map (\x -> (insInd (i , I0) x , x) ) (createTable d)
                       ++ map (\x -> (insInd (i , I1) x , x) ) (createTable d))
  compose (PMap sigma) (PMap tau) = PMap $ Map.compose sigma tau
  isId = all (\(x,y) -> x == y) . Map.toList . pmap
  isFace = isFaceSet . Map.elems . pmap
  rmI (PMap sigma) i = PMap $ Map.map (`rmInd` i) sigma

instance Rs PMap PPMap where
  allPConts _ m n = [ createPPMap m n ]
  unfold = getPMaps
  combine = PPMap . combineMaps . (map pmap)
  -- constrCont :: Ctxt r w -> Ty r w -> Decl r w -> Maybe (Term r w)
  constrCont c gty (p , pty) = do
    sigma <- foldM
                  (\sigma (ie , gf) -> do
                    -- traceM $ show ie ++ " : " ++ show sigma ++ " : " ++ q ++ "<" ++ show tau ++ ">"
                    theta <- case gf of
                        App (Var q) tau | q == p -> (Just . PPMap . injPotMap . pmap) tau
                        _ -> do
                          let theta = filter (\s -> normalise c (App (Var p) s) == gf)
                                      (unfold (PPMap (restrMap (ppmap sigma) ie)))
                          if null theta
                            then Nothing
                            else Just (combine theta)
                    return $ foldl (\s x -> updatePPMap s (insInd ie x) ((ppmap theta) ! x)) sigma (createTable (tyDim gty - 1))
                      )
                  (createPPMap (tyDim gty) (tyDim pty))
                  (sortBy (\(_, s) (_,t) -> compare (baseDim c t) (baseDim c s))
                    [ (ie , getFace gty ie) | ie <- restrictions (tyDim gty) , sideSpec gty ie])

    -- traceShowM (length (getPMaps sigma))
    return (App (Var p) (fstPMap sigma))
