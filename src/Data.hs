{-# LANGUAGE FlexibleInstances #-}
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

-- Use de Brujin indices for variables
type IVar = Int


-- We regard interval substitutions as poset maps
type Subst = Map Vert Vert

-- Get the dimensions of domain and codomain of a substitution
instance Fct Subst where
  domdim = length . toBools . fst . head . Map.toList
  coddim = length . toBools . snd . head . Map.toList


-- Constructor for a constant substitution
constSubst :: IVar -> Subst
constSubst dim = Map.fromList (map (\x -> (x, Vert [])) (createPoset dim))

-- Cubes

data Term = Term Id Subst | Comp Box
  deriving (Eq , Show)

data Box = Box [(Term , Term)] Term
  deriving (Eq , Show)

-- TODO pretty print for terms
-- instance Show Term where
--   show (Term id r) = show id ++ " " ++ show r
--   show (Comp b) = show b -- show sides ++ " " ++ show back

newtype Boundary = Boundary { faces :: [(Term, Term)]}

instance Show Boundary where
  show (Boundary ss) = show ss

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

evalFace :: Cube -> Id -> [Vert] -> Term
evalFace cube f vs =
  let ty = lookupDef cube f in
  case dim ty of
    0 -> Term f (constSubst (log2 (length vs)))
    n -> if any (\u -> head vs `vdiff` u > n-1) (tail vs)
        then Term f (reconstrPMap vs)
        else evalBoundary cube ty vs

evalBoundary :: Cube -> Boundary -> [Vert] -> Term
evalBoundary cube (Boundary fgs) xs =
  let (i , Endpoint e) = getFirstCommon xs in
  let (a , b) = fgs !! (i - 1) in
  let (Term f subst) = if e then b else a in
  evalFace cube f (map (\x -> subst ! removeInd x i) xs)


wellFormedDecl :: Cube -> Decl -> Bool
wellFormedDecl ctxt (Decl id ty) = 
  case dim ty of
    0 -> True -- check no name clash?
    1 -> True -- check that vertices are defined
    _ ->
      let subp = createPoset (dim ty -2) in
      -- trace ("CHECK " ++ id ++ show (dim ty)) -- ++ " over " ++ show ctxt )
      all (\xs ->
        let (i , Endpoint e) = getFirstCommon xs in
        let (j , Endpoint e') = getFirstCommon (map (\x -> removeInd x i) xs) in

        let (Term f subst) = (if e then snd else fst) (faces ty !! (i - 1)) in
        let a = evalFace ctxt f (map (\x -> subst ! removeInd x i) xs) in

        let (Term g subst') = (if e' then snd else fst) (faces ty !! j) in
        let b = evalFace ctxt g (map (\x -> subst' ! removeInd x (j + 1)) xs) in

        -- trace (show xs ++ " : " ++ show (i,e,a) ++ " vs " ++ show (j+1,e',b))
        (a == b)
        ) (getFaces (dim ty) (dim ty - 2))

-- TODO also check for correct dimensions?
wellFormed :: Cube -> Bool
wellFormed cube = all (\i -> wellFormedDecl (Cube (take i (constr cube))) (constr cube !! i)) [0..cdim cube-1]


matchDistortion :: Cube -> Boundary -> Id -> Maybe Term
matchDistortion cube goal f =
  let ty = lookupDef cube f in
  let psubst = foldr
                (\xs sigma ->
                  let a = evalBoundary cube goal xs in
                  let gadgets = map (map snd . Map.toList) (getSubsts (sigma `restrictKeys` Set.fromList xs)) in
                  let gadgets' = filter (\g -> evalFace cube f g == a) gadgets in
                  let vus = map (\i -> nub (map (!!i) gadgets')) [0 .. length xs - 1] in
                  foldl (\s (x , vu) -> updatePSubst s x vu) sigma (zip xs vus)
                  )
                (createPSubst (dim goal) (dim ty))
                (getFaces (dim goal) (dim goal - 1)) in

  if any null (psubst)
    then Nothing
    else Just $ Term f (fstSubst psubst)

findDistortion :: Cube -> Boundary -> Maybe Term
findDistortion ctxt goal = msum (map (\(Decl id _) -> matchDistortion ctxt goal id) (constr ctxt))


-- Potential substitutions have for each element in the domain a list of possible values
type PSubst = Map Vert [Vert]

instance Fct PSubst where
  domdim = length . head . Map.toList
  coddim = undefined -- TODO

-- A potential term is an identifier with potential substitution
data PTerm = PTerm Id PSubst
  deriving (Eq)

instance Show PTerm where
  show (PTerm f part) = show f ++ " " ++ show part

pterm2term :: PTerm -> Term
pterm2term (PTerm f subst) = Term f (fstSubst subst)

-- Given dimensions for domain and codomain, create the most general
-- potential substitution
createPSubst :: Int -> Int -> PSubst
createPSubst k l = Map.fromList $ map (\v -> (v , createPoset l)) (createPoset k)

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
