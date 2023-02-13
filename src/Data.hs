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


-- This data structures are used to internally represent cubes


-- These are the names of faces of a cube
type Id = String

-- Use de Brujin indices for interval variables
type IVar = Int

type Restr = (Int , Endpoint)

-- We regard interval substitutions as poset maps
type Subst = Map Vert Vert

-- Get the dimensions of domain and codomain of a substitution
instance Fct Subst where
  domdim = length . toBools . fst . head . Map.toList
  coddim = length . toBools . snd . head . Map.toList


-- Constructor for a constant substitution
constSubst :: IVar -> Subst
constSubst n = Map.fromList (map (\x -> (x, Vert [])) (createPoset n))

-- Cubes

data Term = Term Id Subst | Comp Box | Filler Box
  deriving (Eq , Show , Ord)


data Box = Box [(Term , Term)] Term
  deriving (Eq , Show , Ord)

termId :: Term -> Id
termId (Term p _) = p

-- TODO pretty print for terms
-- instance Show Term where
--   show (Term id r) = show id ++ " " ++ show r
--   show (Comp b) = show b -- show sides ++ " " ++ show back

newtype Boundary = Boundary { faces :: [(Term, Term)]}
  deriving (Eq , Ord)

instance Show Boundary where
  show (Boundary ss) = show ss

-- instance Foldable Boundary where
--   foldr f z [] = z
--   foldr f z ((p,q):pqs) = f p : f q : (foldr f z pqs)

toList :: Boundary -> [Term]
toList = foldr (\x xs -> fst x : snd x : xs) [] .  faces

dim :: Boundary -> Int
dim = length . faces

containsBox :: Boundary -> Bool
containsBox = any (\t -> case t of {Comp _ -> True; Filler _ -> True; _ -> False}) . toList 

containsFace :: Boundary -> Id -> Bool
containsFace ty p = (any (\t -> case t of {Comp _ -> False; Filler _ -> False; Term q _ -> p == q}) . toList) ty


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
termFace ctxt (Filler (Box pqs r)) (i,Endpoint e) =
  if i == 1
    then if e then Comp (Box pqs r) else r
    else (if e then snd else fst) (pqs !! (i - 2))

termRestr :: Cube -> Term -> [Restr] -> Term
termRestr ctxt t ies = normalize ctxt (foldr (flip (termFace ctxt)) t ies)

inferBoundary :: Cube -> Term -> Boundary
inferBoundary ctxt (Term p sigma) = Boundary $
    map (\i -> (termFace ctxt (Term p sigma) (i, e0), termFace ctxt (Term p sigma) (i, e1)))
        ([1 .. domdim sigma])

inferBoundary ctxt (Comp (Box pqs _)) = Boundary $ map (\(p,q) -> (termFace ctxt p (length pqs,e1) , termFace ctxt q (length pqs,e1)) ) pqs
inferBoundary ctxt (Filler (Box pqs r)) = Boundary $ pqs ++ [(r , Comp (Box pqs r))]


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



boundariesAgree :: [[Vert]] -> Bool
boundariesAgree gadss =
  all (\(xs , overlaps) -> True) 
  (zip (getFaces (length gadss) (length gadss -2)) $ map getAllCommon $ getFaces (length gadss) (length gadss -2))


-- Potential substitutions have for each element in the domain a list of possible values
type PSubst = Map Vert [Vert]

instance Fct PSubst where
  domdim = length . toBools . fst . head . Map.toList
  coddim = undefined -- TODO

-- A potential term is an identifier with potential substitution
data PTerm = PTerm Id PSubst -- | Fixed Term
  deriving (Eq)

instance Show PTerm where
  show (PTerm f part) = show f ++ " " ++ show part
  -- show (Fixed t) = show t

pterm2term :: PTerm -> Term
pterm2term (PTerm f subst) = Term f (fstSubst subst)
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

createPTerm :: Decl -> Int -> PTerm
createPTerm (Decl f ty) gdim =
  let img = createPoset (dim ty) in
  let parts = map (\v -> (v , img)) (createPoset gdim) in
  PTerm f (Map.fromList parts)


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
possibleFaces :: Cube -> PTerm -> [Restr] -> [(Subst , Term)]
-- possibleFaces ctxt (PTerm p sigma) ies | trace ("myfun " ++ show (PTerm p sigma) ++ " " ++ show ies) False = undefined
possibleFaces ctxt (PTerm p sigma) ies = let ss = getSubsts sigma in
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
filterPSubst :: Cube -> PTerm -> [Restr] -> [Term] -> Maybe PSubst
filterPSubst ctxt (PTerm p sigma) ies qs =
  let ss = [ s | (s , q) <- possibleFaces ctxt (PTerm p sigma) ies , q `elem` qs ] in
  let sigma' = updateGadgets sigma ss ies in
  if isEmptyPSubst sigma'
    then Nothing
    else Just sigma'
