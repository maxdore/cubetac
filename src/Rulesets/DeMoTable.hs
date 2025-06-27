{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Rulesets.DeMoTable where

import qualified Data.Map as Map
import Data.Map ((!))
import Data.List
import Control.Monad

import Prel
import Core
import Poset

import Debug.Trace


data Four = F0 | U | V | F1
  deriving (Eq, Show , Ord)

negFour :: Four -> Four
negFour F0 = F1
negFour F1 = F0
negFour U = U
negFour V = V

intToFour :: Endpoint -> Four
intToFour I0 = F0
intToFour I1 = F1

type FourVert = [Four]

type FourTable = [FourVert]

-- Construct I^n poset
createFourTable :: Int -> FourTable
createFourTable n | n <= 0 = [[]]
createFourTable n = let g = (createFourTable (n - 1))
  in map (F0 :) g ++ map (U :) g ++ map (V :) g ++ map (F1 :) g

-- Given an element in a poset, remove the i-th index from it
rmIndFour :: FourVert -> Int -> FourVert
rmIndFour ((_:es)) 1 = es
rmIndFour ((e:es)) n = e : (rmIndFour es (n-1))
rmIndFour _ _ = error "This index is not part of the element"

-- Insert e such that x_i = e afterwards
insIndFour :: Restr -> FourVert -> FourVert
insIndFour (0 , _) _ = error "Indices start from 1"
insIndFour (i , e) es | i > length es + 1 = error "Index too large for element"
                  | otherwise = let (f,s) = splitAt (i-1) es in (f ++ [intToFour e] ++ s)


isFaceSetFour :: [FourVert] -> Maybe Restr
isFaceSetFour vs
  | null (head vs) = Nothing
  | all ((== F1) . head) vs = Just (1 , I1)
  | all ((== F0) . head) vs = Just (1 , I0)
  | otherwise = case isFaceSetFour (map tail vs) of
      Nothing -> Nothing
      Just (i , e) -> Just (i + 1 , e)



-- for Boolean/DeMorgan

newtype DeMoTable = DeMoTable {dmt :: Map.Map Vert FourVert} deriving (Eq,Show,Ord)

instance Fct DeMoTable where
  domdim = length . fst . head . Map.toList . dmt
  coddim = length . snd . head . Map.toList . dmt

-- The type of potential poset maps
newtype PDeMoTable = PDeMoTable {pdmt :: Map.Map Vert [FourVert]} deriving (Eq,Show,Ord)

instance Fct PDeMoTable where
  domdim = length . fst . head . Map.toList . pdmt
  coddim = length . head . snd . head . Map.toList . pdmt

createPDeMoTable :: Int -> Int -> PDeMoTable
createPDeMoTable k l = PDeMoTable $ Map.fromList $ map (\v -> (v , createFourTable l)) (createTable k)

getDeMoTables :: PDeMoTable -> [DeMoTable]
getDeMoTables (PDeMoTable sigma) = map (DeMoTable . Map.fromList) (helper (Map.toList sigma))
  where
  helper :: [(Vert , [FourVert])] -> [[(Vert , FourVert)]]
  helper [] = [[]]
  helper ((x , vs) : ys) = [ (x , v) : r | v <- vs , r <- helper ys ]

updatePDeMoTable :: PDeMoTable -> Vert -> [FourVert] -> PDeMoTable
updatePDeMoTable (PDeMoTable sigma) x vs = PDeMoTable $ Map.insert x vs sigma


-- instance Bs DeMoTable where
--   tdim sigma = domdim sigma
--   face (DeMoTable sigma) r = DeMoTable (restrMap sigma r)
--   deg d i = DeMoTable $ Map.fromList (map (\x -> (insInd (i , I0) x , map intToFour x) ) (createTable d)
--                        ++ map (\x -> (insInd (i , I1) x , map intToFour x) ) (createTable d))
--   compose (DeMoTable sigma) (DeMoTable tau) = DeMoTable $ Map.compose sigma tau
--   isId = all (\(x,y) -> x == y) . Map.toList . dmt
--   isFace = isFaceSetFour . Map.elems . dmt
--   rmI (DeMoTable sigma) i = DeMoTable $ Map.map (`rmIndFour` i) sigma

-- instance Rs DeMoTable PDeMoTable where
--   allPConts _ m n = [ createPDeMoTable m n ]
--   unfold = getDeMoTables
--   combine = PDeMoTable . combineMaps . (map dmt)

--   constrCont c gty (p , pty) = do
--     sigma <- foldM
--                   (\sigma (ie , gf) -> do
--                     -- traceM $ show ie ++ " : " ++ show sigma ++ " : " ++ q ++ "<" ++ show tau ++ ">"
--                     theta <- case gf of
--                         App (Var q) tau | q == p -> (Just . PDeMoTable . injPotMap . dmt) tau
--                         _ -> do
--                           let theta = filter (\s -> normalise c (App (Var p) s) == gf)
--                                       (unfold (PDeMoTable (restrMap (pdmt sigma) ie)))
--                           if null theta
--                             then Nothing
--                             else Just (combine theta)
--                     return $ foldl (\s x -> updatePDeMoTable s (insIndFour ie x) ((pdmt theta) ! x)) sigma (createTable (tyDim gty - 1))
--                       )
--                   (createPDeMoTable (tyDim gty) (tyDim pty))
--                   (sortBy (\(_, s) (_,t) -> compare (baseDim c t) (baseDim c s))
--                     [ (ie , getFace gty ie) | ie <- restrictions (tyDim gty) , sideSpec gty ie])

--     -- traceShowM (length (getPMaps sigma))
--     let sols = (getDeMoTables sigma) -- TODO filter
--     return (App (Var p) (head sols))



  -- solve twop invGoal :: Term DeMoTable PDeMoTable
