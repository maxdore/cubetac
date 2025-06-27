{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Rulesets.DeMo where

import qualified Data.Map as Map
import Data.Map ((!), Map)
import Data.List
import Control.Monad

import Prel
import Poset
import Core

import Debug.Trace

data Atom = Pos IVar | Neg IVar
  deriving (Show, Ord, Eq)

-- We save formulas as tuples of conjunctions of disjunctions of literals
type DeMo = (IVar , [[[Atom]]])

a2i :: Atom -> IVar
a2i (Pos i) = i
a2i (Neg i) = i

mapAtom :: (IVar -> IVar) -> Atom  -> Atom
mapAtom f (Pos i) = Pos (f i)
mapAtom f (Neg i) = Neg (f i)

negAtom :: Atom -> Atom
negAtom (Pos i) = Neg i
negAtom (Neg i) = Pos i


offset :: IVar -> [[[Atom]]] -> [[[Atom]]]
offset i = map (map (map (\j -> if a2i j < i then j else mapAtom (\a -> a - 1) j)))

redDnf :: [[Atom]] -> [[Atom]]
redDnf r =
  let r' = map (nubBy (\d d' -> a2i d == a2i d')) (map nub r) in
  filter (\d -> not (any (\d' -> d /= d' && intersect d d' == d) r')) r'

inDnf :: [[Atom]] -> Bool
inDnf phi = all (\c -> all (\d -> c == d || c \\ d /= []) phi) phi

allForm :: Dim -> Dim -> [DeMo]
allForm m n = map (\rs -> (m , rs)) (replicateM n rss)
  where
    subsets :: [IVar] -> [[Atom]]
    subsets [ i ] = [[ Pos i ] , [Neg i]]
    subsets (i : is) = let r = subsets is in
      [[Pos i] , [Neg i]] ++ r ++ map (Pos i:) r ++ map (Neg i:) r
    rss = filter inDnf (ps (subsets [1..m]))


subst :: [[Atom]] -> IVar -> [[Atom]] -> [[Atom]]
subst cs i ds =
  let res =
        [ delete (Pos i) c ++ d | c <- cs , Pos i `elem` c , d <- ds ] ++
        [ delete (Neg i) c ++ map negAtom d | c <- cs , Neg i `elem` c , d <- ds ] ++
        [ c | c <- cs , Pos i `notElem` c , Neg i `notElem` c ] in
    redDnf res

-- form2subst :: DeMo -> TruthTable
-- form2subst (m , rs) = TruthTable $ Map.fromList (map (\v -> (v , (map (evalFormula v) rs))) (createTable m))
--   where
--   evalFormula :: Vert -> [[Atom]] -> Endpoint
--   evalFormula is ds =
--     let vs1 = map fst $ filter (toBool . snd) (zip [1..] is) in
--     let result = map (\d -> filter (\i -> i `notElem` vs1) d) ds in
--     fromBool $ [] `elem` result


-- subst2form :: PMap -> DeMo
-- subst2form (PMap s) =
--   (domdim (PMap s) , reverse $ map (\fi -> constrFormula (map (\(x , is) -> (x , is !! fi)) (Map.toList s))) [0 .. coddim (PMap s)-1])
--     where
--     constrFormula :: [(Vert , Endpoint)] -> [[IVar]]
--     constrFormula ves =
--       let truevs = [ v | (v , e) <- ves , toBool e ] in
--       let cs = [ [ i | (e,i) <- zip vs [1..] , toBool e] | vs <- truevs ] in
--       let redcs = filter (\c -> not (any (\d -> c /= d && d `isSubsequenceOf` c) cs)) cs in
--       let normcs = sort redcs in
--         normcs



instance Bs DeMo where
  tdim (m , rs) = m
  face (m , rs) (i,e) =
    let rs' = if e == I0
                  then map (map (delete (Neg i))) (map (filter (Pos i `notElem`)) rs)
                  else map (map (delete (Pos i))) (map (filter (Neg i `notElem`)) rs)
    in (m-1, offset i rs')

  deg d i =  (d+1 , [ [[Pos j]] | j <- [1..d+1] , j /= i])

  compose (m , ss) (n , rs) =
    let rs' = map (map (map (mapAtom (\i -> i + m)))) rs in
    let ss' = map (\d -> foldr (\i d' -> subst d' i (rs'!!(i-1))) d [1..n]) ss in
    (((n , map (map (map (mapAtom (\i -> i - m)))) ss')))

  isId (m , rs) = rs == [ [[Pos i]] | i <- [1..m]]

  isFace (m , rs) = case findIndex null rs of
    Just i -> Just (i+1,I0)
    Nothing -> case findIndex ([] `elem`) rs of
      Just i -> Just (i+1,I1)
      Nothing -> Nothing

  rmI (m , rs) i = (m , take (i-1) rs ++ drop i rs)

  allConts = allForm



-- instance Rs DeMo PTruthTable where
--   allPConts _ m n = [ createPTruthTable m n ]
--   unfold = map subst2form . getTruthTables
--   combine = PTruthTable . combineMaps . (map (tt . form2subst))

--   constrCont c gty (p , pty) = do
--     sigma <- foldM
--                   (\sigma (ie , gf) -> do
--                     -- traceM $ show ie ++ " : " ++ show sigma ++ " : " ++ q ++ "<" ++ show tau ++ ">"
--                     theta <- case gf of
--                         App (Var q) tau | q == p -> (Just . PTruthTable . injPotMap . tt) tau
--                         _ -> do
--                           let theta = filter (\s -> normalise c (App (Var p) s) == gf)
--                                       (unfold (PTruthTable (restrMap (ptt sigma) ie)))
--                           if null theta
--                             then Nothing
--                             else Just (combine theta)
--                     return $ foldl (\s x -> updatePTruthTable s (insInd ie x) ((ptt theta) ! x)) sigma (createTable (tyDim gty - 1))
--                       )
--                   (createPTruthTable (tyDim gty) (tyDim pty))
--                   (sortBy (\(_, s) (_,t) -> compare (baseDim c t) (baseDim c s))
--                     [ (ie , getFace gty ie) | ie <- restrictions (tyDim gty) , sideSpec gty ie])

--     let sols = (getTruthTables sigma) -- TODO filter
--     return (App (Var p) (subst2form (head sols)))


