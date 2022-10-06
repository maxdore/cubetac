{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Data where

import Data.List
import qualified Data.Map as Map
import Data.Map ((!), Map)

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

newtype Type = Type { faces :: [(Term, Term)]}

instance Show Type where
  show (Type ss) = show ss

dim :: Type -> Int
dim = length . faces

data Decl = Decl Id Type

instance Show Decl where
  show (Decl id ty) = show id ++ " : " ++ show ty

decl2pair :: Decl -> (Id , Type)
decl2pair (Decl id ty) = (id , ty)

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
  show (PTerm id part) = show id ++ " " ++ show part


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
  filterRec x v ys = map (\(y, us) -> (y , [ u | u <- us , (y `below` x) --> (u `below` v) ])) ys


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
injPSubst = Map.map (\v -> [v])

createPTerm :: Decl -> Int -> PTerm
createPTerm (Decl id ty) gdim =
  let img = createPoset (dim ty) in
  let parts = map (\v -> (v , img)) (createPoset gdim) in
  PTerm id (Map.fromList parts)

