{-# LANGUAGE FlexibleInstances  #-}
module Data where

import Control.Monad
import Data.Map.Strict (Map, (!), restrictKeys)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.List

import Prel
import Poset

import Debug.Trace


-- These are the names of faces of a cube
type Id = String

-- Use de Brujin indices for interval variables
type IVar = Int

type Restr = (IVar , Endpoint)

restrictions :: Int -> [Restr]
restrictions n = [ (i,e) | i <- [1..n], e <- [e0,e1]]

data BoxFace = Back | Side Restr
  deriving (Show, Eq , Ord)

-- We regard interval substitutions as poset maps
type Subst = Map Vert Vert

-- Get the dimensions of domain and codomain of a substitution
instance Fct Subst where
  domdim = length . toBools . fst . head . Map.toList
  coddim = length . toBools . snd . head . Map.toList



-- Cubes

data Term = Term Id Subst | Comp Box | Fill Box | Free
  deriving (Eq , Show , Ord)

data Box = Box [(Term , Term)] Term
  deriving (Eq , Show , Ord)

modifyBox :: Box -> (Restr -> Term -> Term) -> (Term -> Term) -> Box
modifyBox (Box sts b) sides back = 
  Box (map (\i -> ( sides (i,e0) (fst (sts!!(i-1))) , sides (i,e1) (snd (sts!!(i-1))) ) ) [1..length sts]) (back b)


-- foldBox :: Box -> (Restr -> Term -> a) -> (Term -> b) -> ([a],b)
-- foldBox (Box sts b) sides back = let b' = back b in
--   where
--     foldsides :: [(Term,Term)] -> [a]
--     foldsides [] = []
--     foldsides 


-- Also works if back boundary is Free
getBackBoundary :: Cube -> Box -> Boundary
getBackBoundary ctxt (Box sts _) = let n = length sts in
  Boundary $ map (\(s,t) -> (termFace ctxt s (n , e0) , termFace ctxt t (n , e0))) sts

getSideBoundary :: Cube -> Boundary -> Box -> Restr -> Boundary
getSideBoundary ctxt front (Box sts b) (i,e) = let n = length sts in
  trace (show b) $
  Boundary $ (map (\j -> let st = sts!!(j-1) in
                                trace (show (i,e) ++ " " ++ show j) $ 
                                (termFace ctxt (fst st) (1,e) , termFace ctxt (snd st) (1,e))) [ j | j <- [1..n], j /= i])
            ++ [(termFace ctxt b (i,e) , boundaryFace front (i,e))]


checkBoundaries :: Cube -> Term -> Restr -> Term -> Restr -> Bool
checkBoundaries ctxt s ie t jf =
  let u = termFace ctxt s ie in
  let v = termFace ctxt t jf in
  if u == v || u == Free || v == Free
    then True
    else trace ("BOUNDARIES DONT AGREE " ++ show s ++ "@" ++ show ie ++ " AND " ++ show t ++ "@" ++ show jf ++ "\n" ++ show u ++ " IS NOT " ++ show v) False


wellFormedBox :: Cube -> Box -> Bool
wellFormedBox ctxt (Box sts b) = all (\(i,(s,t)) -> fits s (i,e0) && fits t (i,e1)) (zip [1..n] sts)
  where
    n = length sts
    fits :: Term -> Restr -> Bool
    fits u (i,e) = checkBoundaries ctxt u (length sts,e0) b (i,e) &&
                   all (\j -> let (v,w) = sts!!(j) in
                              checkBoundaries ctxt u (j,e0) v (i,e) &&
                              checkBoundaries ctxt u (j,e1) w (i,e)
                              ) [ j | j <- [i..n-1] ]



termId :: Term -> Id
termId (Term p _) = p


newtype Boundary = Boundary { faces :: [(Term, Term)]}
  deriving (Eq , Ord)

instance Show Boundary where
  show (Boundary ss) = show ss


toList :: Boundary -> [Term]
toList = foldr (\x xs -> fst x : snd x : xs) [] .  faces

dim :: Boundary -> Int
dim = length . faces


data Decl = Decl Id Boundary

instance Show Decl where
  show (Decl f ty) = show f ++ " : " ++ show ty

decl2pair :: Decl -> (Id , Boundary)
decl2pair (Decl f ty) = (f , ty)

newtype Cube = Cube { constr :: [Decl]}

instance Show Cube where
  show (Cube fc) = show fc

cdim :: Cube -> Int
cdim = length . constr

lookupDef :: Cube -> Id -> Boundary
lookupDef cube name =
  case lookup name (map decl2pair (constr cube)) of
    Just face -> face
    Nothing -> error $ "Could not find definition of " ++ name

tdim :: Term -> Int
tdim (Term _ s) = domdim s

normalize :: Cube -> Term -> Term
normalize ctxt (Term p sigma) =
  case isSubposet (Map.elems sigma) of
    Nothing -> Term p sigma
    Just (i , e) ->
      let (Term q tau) = boundaryFace (lookupDef ctxt p) (i,e) in
      let si = Map.map (`removeInd` i) sigma in
      normalize ctxt (Term q (Map.compose tau si))
normalize _ b = b

inNf :: Cube -> Term -> Bool
inNf ctxt (Term p sigma) = p == termId (normalize ctxt (Term p sigma))


boundaryFace :: Boundary -> Restr -> Term
boundaryFace (Boundary ty) (i , Endpoint e) = (if e then snd else fst) (ty !! (i-1))


isFree , isComp :: Term -> Bool
isFree Free = True
isFree _ = False
isComp (Comp _) = True
isComp _ = False

getFreeFaces :: Boundary -> [Restr]
getFreeFaces ty = filter (\ie -> isFree (boundaryFace ty ie)) (restrictions (dim ty))

getCompFaces :: Boundary -> [Restr]
getCompFaces ty = filter (\ie -> isComp (boundaryFace ty ie)) (restrictions (dim ty))

containsBox :: Boundary -> Bool
containsBox = any (\t -> case t of {Comp _ -> True; Fill _ -> True; _ -> False}) . toList

containsFace :: Boundary -> Id -> Bool
containsFace ty p = (any (\t -> case t of {Comp _ -> False; Fill _ -> False; Term q _ -> p == q}) . toList) ty



termFace :: Cube -> Term -> Restr -> Term
termFace ctxt (Term p sigma) (i,e) =
  if i == 0
    then error "Indices of faces start at 1"
    else
      let subpos = map (insInd i e) (createPoset (domdim sigma - 1)) in
      let subsigma = sigma `restrictKeys` Set.fromList subpos in
      let sigma' = Map.mapKeys (`removeInd` i) subsigma in
      normalize ctxt (Term p sigma')

termFace ctxt (Comp (Box pqs r)) (i,Endpoint e) =
  let a = (if e then snd else fst) (pqs !! (i-1)) in
  termRestr ctxt a [(length pqs , e1)]

termFace ctxt (Fill (Box pqs r)) (i,Endpoint e) =
  if i == length pqs + 1
    then if e then Comp (Box pqs r) else r
    else (if e then snd else fst) (pqs !! (i - 1))

termFace _ Free _ = Free

termRestr :: Cube -> Term -> [Restr] -> Term
termRestr ctxt t ies = normalize ctxt (foldr (flip (termFace ctxt)) t ies)

inferBoundary :: Cube -> Term -> Boundary
inferBoundary ctxt (Term p sigma) = Boundary $
    map (\i -> (termFace ctxt (Term p sigma) (i, e0), termFace ctxt (Term p sigma) (i, e1)))
        ([1 .. domdim sigma])

inferBoundary ctxt (Comp (Box pqs _)) = Boundary $ map (\(p,q) -> (termFace ctxt p (length pqs,e1) , termFace ctxt q (length pqs,e1)) ) pqs
inferBoundary ctxt (Fill (Box pqs r)) = Boundary $ pqs ++ [(r , Comp (Box pqs r))]


matchesBoundary :: Cube -> Term -> Boundary -> Bool
matchesBoundary ctxt t goal = let ty = inferBoundary ctxt t in
  all (\(s , t) -> s == Free || s == t) (zip (toList goal) (toList ty))


-- boundariesAgree :: [[Vert]] -> Bool
-- boundariesAgree gadss =
--   all (\(xs , overlaps) -> True)
--   (zip (getFaces (length gadss) (length gadss -2)) $ map getAllCommon $ getFaces (length gadss) (length gadss -2))



-- wellFormedDecl :: Cube -> Decl -> Bool
-- wellFormedDecl ctxt (Decl id ty) =
--   case dim ty of
--     0 -> True -- check no name clash?
--     1 -> True -- check that vertices are defined
--     _ ->
--       -- trace ("CHECK " ++ id ++ show (dim ty)) -- ++ " over " ++ show ctxt )
--       all (\xs ->
--         let (i , Endpoint e) = getFirstCommon xs in
--         let (j , Endpoint e') = getFirstCommon (map (`removeInd` i) xs) in

--         let (Term f subst) = (if e then snd else fst) (faces ty !! (i - 1)) in
--         let a = evalFace ctxt f (map (\x -> subst ! removeInd x i) xs) in

--         let (Term g subst') = (if e' then snd else fst) (faces ty !! j) in
--         let b = evalFace ctxt g (map (\x -> subst' ! removeInd x (j + 1)) xs) in

--         -- trace (show xs ++ " : " ++ show (i,e,a) ++ " vs " ++ show (j+1,e',b))
--         (a == b)
--         ) (getFaces (dim ty) (dim ty - 2))

-- TODO also check for correct dimensions?
-- wellFormed :: Cube -> Bool
-- wellFormed cube = all (\i -> wellFormedDecl (Cube (take i (constr cube))) (constr cube !! i)) [0..cdim cube-1]


-- Common term constructions
deg :: Term -> Term
deg (Term p sigma) = Term p $ Map.fromList (Map.toList (Map.mapKeys (insInd 1 e0) sigma) ++ Map.toList (Map.mapKeys (insInd 1 e1) sigma))

pinv :: Cube -> Term -> Box
pinv ctxt p = Box [(p , deg (termFace ctxt p (1,e0)))] (deg (termFace ctxt p (1,e0)))

pcomp :: Cube -> Term -> Term -> Box
pcomp ctxt p q | termFace ctxt p (1,e1) /= termFace ctxt q (1,e0) =
                  error $ "Boundaries of composed paths do not match at" ++ show p ++ " . " ++ show q
               | otherwise = Box [(deg (termFace ctxt p (1,e0)) , q)] p


-- Constructor for a constant substitution
constSubst :: IVar -> Subst
constSubst n = Map.fromList (map (\x -> (x, Vert [])) (createPoset n))






-- Potential substitutions have for each element in the domain a list of possible values
type PSubst = Map Vert [Vert]

instance Fct PSubst where
  domdim = length . toBools . fst . head . Map.toList
  coddim = undefined -- TODO

-- A potential term is an identifier with potential substitution
data PContortion = PContortion Id PSubst
  deriving (Eq)

instance Show PContortion where
  show (PContortion f part) = show f ++ " " ++ show part
  -- show (Fixed t) = show t

pterm2term :: PContortion -> Term
pterm2term (PContortion f subst) = Term f (fstSubst subst)
-- pterm2term (Fixed t) = t

-- Given dimensions for domain and codomain, create the most general
-- potential substitution
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

createPContortion :: Decl -> Int -> PContortion
createPContortion (Decl f ty) gdim =
  let img = createPoset (dim ty) in
  let parts = map (\v -> (v , img)) (createPoset gdim) in
  PContortion f (Map.fromList parts)


-- Given a potential substitution, restrict the values of x to vs
-- and make sure that the map is still a poset map
updatePSubst :: PSubst -> Vert -> [Vert] -> PSubst
updatePSubst sigma x vs = Map.mapWithKey (\y us -> filter (\u ->
                                                        (y `above` x) --> any (u `above`) vs &&
                                                        (y `below` x) --> any (u `below`) vs
                                                      ) us) (Map.insert x vs sigma)

isEmptyPSubst :: PSubst -> Bool
isEmptyPSubst sigma = any (null . snd) (Map.toList sigma)


-- Given a pterm, what could its faces be?
possibleFaces :: Cube -> PContortion -> [Restr] -> [(Subst , Term)]
-- possibleFaces ctxt (PContortion p sigma) ies | trace ("myfun " ++ show (PContortion p sigma) ++ " " ++ show ies) False = undefined
possibleFaces ctxt (PContortion p sigma) ies = let ss = getSubsts sigma in
  -- trace ("UNFOLDING " ++ show (length ss)) $
  map (\s -> (s , termRestr ctxt (Term p s) ies)) ss

-- possibleFaces ctxt (Fixed t) ies = [(undefined , termRestr ctxt t ies)]


updateGadgets :: PSubst -> [Subst] -> [Restr] -> PSubst
updateGadgets sigma ss ies =
  let xs = createPoset (domdim sigma) in
  let vus = map (\x -> nub (map (! x) ss)) xs in -- TODO TAKE INTO ACCOUNT RESTRICTIONS!
  foldl (\s (x , vu) -> updatePSubst s x vu) sigma (zip xs vus)

-- Given a pterm, filter it so that it some face of it is contained in a
-- collection of terms
filterPSubst :: Cube -> PContortion -> [Restr] -> [Term] -> Maybe PContortion
filterPSubst ctxt (PContortion p sigma) ies qs =
  let ss = [ s | (s , q) <- possibleFaces ctxt (PContortion p sigma) ies , q `elem` qs ] in
  let sigma' = updateGadgets sigma ss ies in
  if isEmptyPSubst sigma'
    then Nothing
    else Just (PContortion p sigma')
