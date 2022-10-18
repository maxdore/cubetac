{-# LANGUAGE FlexibleInstances #-}
module Data where

import qualified Data.Map as Map
import Data.Map (Map)

import Prel
import Poset

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



-- Check fibrancy of extension types: cofibration only mentions interval variables which are bound in the extension type https://discord.com/channels/954089080197611551/1007614554647306240/1010200102469632010
-- TODO IMPLEMENT!



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
