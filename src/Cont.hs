{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Cont where

import qualified Data.Map as Map
import Data.Map ((!), Map)
import Data.List
import Data.Maybe

import Prel
import Core

import Debug.Trace

-- An element of a poset is a list of 0s and 1s
newtype Vert = Vert { toBools :: [Endpoint]}
  deriving (Eq , Ord)

instance Show Vert where
  show (Vert []) = "()"
  show (Vert es) = concatMap (\e -> if e == I0 then "0" else "1") es
  -- show (Vert es) = "(" ++ concatMap (\e -> if e == I0 then "0" else "1") es ++ ")"

type Poset = [Vert]

insv :: Endpoint -> Vert -> Vert
e `insv` x = Vert (e: toBools x)

-- Construct an n-element poset
createPoset :: Int -> Poset
createPoset n | n <= 0 = [Vert []]
createPoset n = let g = map toBools (createPoset (n - 1))
  in map (\v -> Vert (I0 : v)) g ++ map (\v -> Vert (I1 : v)) g

-- Given m and n, generate all n-dimensional faces of the m-element poset
getFaces :: Int -> Int -> [[Vert]]
getFaces m 0 = map (: []) (createPoset m)
getFaces m n | m == n = [ createPoset m ]
getFaces m n =
  map (map (I0 `insv`)) (getFaces (m-1) n)
  ++ map (map (I1 `insv`)) (getFaces (m-1) n)
  ++ map (\l -> map (I0 `insv`) l ++ map (I1 `insv`) l) (getFaces (m-1) (n-1))

-- Given two elements of a poset, compute the number of indices in which they differ
-- E.g., vdiff v u == 1 means that v and u are adjacent
vdiff :: Vert -> Vert -> Int
vdiff (Vert []) (Vert []) = 0
vdiff (Vert (e:es)) (Vert (e':es')) = (if e == e' then 0 else 1) + vdiff (Vert es) (Vert es')
vdiff _ _ = error "Comparing difference between elements of different posets"

-- Checking order between two elements of a poset
below , above , dirabove :: Vert -> Vert -> Bool
x `below` y = all (\(e , e') -> toBool e' --> toBool e) (zip (toBools x) (toBools y))
x `above` y = y `below` x
x `dirabove` y = x `above` y && vdiff x y == 1

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




-- Given a list of vertices, return the first index at which all vertices
-- have the same value, as well as that value
getFirstCommon :: [Vert] -> (Int , Endpoint)
getFirstCommon vs
  | all ((== I1) . head . toBools) vs = (1 , I1)
  | all ((== I0) . head . toBools) vs = (1 , I0)
  | otherwise = let (i , e) = getFirstCommon (map (Vert . tail . toBools) vs) in (i + 1 , e)

getAllCommon :: [Vert] -> [(Int , Endpoint)]
getAllCommon vs = if length vs > length (toBools (head vs)) -- TODO NOT CORRECT
  then []
  else
    let (i,e) = getFirstCommon vs in
    (i,e) : map (\(j,e') -> (j+ 1, e')) (getAllCommon (map (\v -> removeInd v i) vs))


-- Given an element in a poset, remove the i-th index from it
removeInd :: Vert -> Int -> Vert
removeInd (Vert (_:es)) 1 = Vert es
removeInd (Vert (e:es)) n = Vert (e : toBools (removeInd (Vert es) (n-1)))
removeInd _ _ = error "This index is not part of the element"

-- Insert e such that x_i = e afterwards
insInd :: Int -> Endpoint -> Vert -> Vert
insInd 0 _ _ = error "Indices start from 1"
insInd i e (Vert es) | i > length es + 1 = error "Index too large for element"
                     | otherwise = let (f,s) = splitAt (i-1) es in Vert (f ++ [e] ++ s)

-- Given a list of n^2 elements of a poset, generate map from [1]^n to the elements
reconstrPMap :: [Vert] -> Map Vert Vert
reconstrPMap vs = Map.fromList (zip (createPoset (log2 (length vs))) vs)



-- We regard interval substitutions as poset maps
type Subst = Map Vert Vert

-- Get the dimensions of domain and codomain of a substitution
instance Fct Subst where
  domdim = length . toBools . fst . head . Map.toList
  coddim = length . toBools . snd . head . Map.toList

type PSubst = Map Vert [Vert]

instance Fct PSubst where
  domdim = length . toBools . fst . head . Map.toList
  coddim = undefined -- TODO


createPSubst :: Int -> Int -> PSubst
createPSubst k l = Map.fromList $ map (\v -> (v , createPoset l)) (createPoset k)


-- Give back restriction of sigma and forget that it was a restriction
restrPSubst :: PSubst -> Restr -> PSubst
restrPSubst sigma (i,e) = Map.mapKeys (`removeInd` i) (Map.filterWithKey (\x _ -> e == toBools x !! (i-1)) sigma)

-- Given a potential substitution, generate all possible substitutions from it
getSubsts :: PSubst -> [Subst]
getSubsts sigma = map Map.fromList (getSubsts' (Map.toList sigma))
  where
  getSubsts' :: [(Vert , [Vert])] -> [[(Vert , Vert)]]
  getSubsts' [] = [[]]
  getSubsts' ((x , vs) : ys) = [ (x , v) : r | v <- vs , r <- getSubsts' (filterRec x v ys) ]

  filterRec :: Vert -> Vert -> [(Vert , [Vert])] -> [(Vert , [Vert])]
  filterRec x v = map (\(y, us) -> (y , [ u | u <- us , (y `below` x) --> (u `below` v) ]))

combineSubsts :: [Subst] -> PSubst
combineSubsts ss = Map.fromList (map (\x -> (x , nub (map (Map.findWithDefault undefined x) ss))) (createPoset (domdim (head ss))))

-- Given a potential substitution, generate the substitution from it
-- (could be equivalently head of getSubsts)
fstSubst :: PSubst -> Subst
fstSubst = Map.fromList . fstPSubst' . Map.toList
  where
  fstPSubst' :: [(Vert , [Vert])] -> [(Vert , Vert)]
  fstPSubst' [] = []
  fstPSubst' ((x,vs) : yws) = (x , head vs) :
    fstPSubst' (map (\(y , ws) -> (y , filter (\w -> (y `below` x) --> (w `below` head vs)) ws)) yws)

injPSubst :: Subst -> PSubst
injPSubst = Map.map (: [])

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

normalise :: Ctxt Cont PCont -> Term Cont PCont -> Maybe (Term Cont PCont)
normalise c (App ((App t tau)) sigma) = normalise c (App t (Map.compose tau sigma))
normalise c (App t s) =
  if isId s
    then normalise c t
    else
      case isSubposet (Map.elems s) of
        Nothing -> Just (App t s)
        Just (i,e) ->
          let ty = inferTy c t in
          if sideSpec ty (i,e)
            then normalise c (App (getFace ty (i,e)) (Map.map (`removeInd` i) s))
            else Nothing

normalise c t = Just t

type PCont = PSubst


instance Rs Cont PCont where
  infer c t s =
    let ty@(Ty n phi) = inferTy c t in
    let m = domdim s in
    let tup = [1..domdim s] :: [IVar] in
    Ty m [ (i,e) +> f | i <- [1..m] , e <- [I0,I1] , f <- maybeToList (normalise c (App t (restrSubst s (i,e)))) ]

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


xdeg :: Term Cont PCont
xdeg = App (Var "x") (Map.fromList [(Vert [I0], Vert []) , (Vert [I1], Vert [])])


andOrSubst = Map.fromList [
              (Vert [I0, I0] , Vert [I0, I0])
            , (Vert [I0, I1] , Vert [I0, I1])
            , (Vert [I1, I0] , Vert [I0, I1])
            , (Vert [I1, I1] , Vert [I1, I1])
              ]
andOrp:: Term Cont PCont
andOrp = App (Var "p") andOrSubst

test :: Term Cont PCont
test = deg twop pqComp 1
