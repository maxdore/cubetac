module Data where

import Data.List
import qualified Data.Map as Map
import Data.Map ((!), Map)

import Prel

-- This file contains the basic data structures used for representing cubes


-- Formulas

-- Use de Brujin indices for variables
type IVar = Int

-- These are the names of faces of a cube
type Id = String

newtype Conj = Conj {literal :: IVar}
  deriving (Eq , Ord)

instance Show Conj where
  show (Conj i) = show i

newtype Disj = Disj {literals :: [Conj]}
  deriving (Eq , Ord)

instance Show Disj where
  show (Disj is) = "(" ++ (concat $ intersperse " /\\ " (map show is)) ++ ")"

newtype Formula = Formula {clauses :: [Disj]}
  deriving (Eq , Ord)

instance Show Formula where
  show (Formula cs) = "(" ++ (concat $ intersperse " \\/ " (map show cs)) ++ ")"

-- Tuples of formulas in DNF
newtype Tele = Tele {formulas :: [Formula]}
  deriving (Eq , Ord)

instance Show Tele where
  show (Tele rs) = concat $ intersperse " " (map show rs)



-- Cubes

data Term = Term Id Tele | Comp Box
  deriving (Eq , Show)

data Box = Box [(Term , Term)] Term
  deriving (Eq , Show)

-- TODO pretty print for terms
-- instance Show Term where
--   show (Term id r) = show id ++ " " ++ show r
--   show (Comp b) = show b -- show sides ++ " " ++ show back

newtype Point = Point { point :: Id }
  deriving (Eq , Show)

-- Constructor for a constant point
emptT :: Id -> Term
emptT face = Term face (Tele [])

-- Constructor for a 1-path with single variable application
idT :: Id -> IVar -> Term
idT face i = Term face (Tele [Formula [ Disj [Conj i]]])

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

