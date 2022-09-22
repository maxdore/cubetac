{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Data where

import Data.List
import qualified Data.Map as Map
import Data.Map ((!), Map)

import Prel


-- Formulas

type Var = Int
type Id = String

newtype Conj = Conj {literal :: Var}
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

newtype Tele = Tele {formulas :: [Formula]}
  deriving (Eq , Ord)

instance Show Tele where
  show (Tele rs) = concat $ intersperse " " (map show rs)




-- Substitutions

newtype Endpoint = Endpoint {toBool :: Bool}
  deriving (Eq , Ord)

instance Show Endpoint where
  show (Endpoint False) = "0"
  show (Endpoint True) = "1"

e0 , e1 :: Endpoint
e0 = Endpoint False
e1 = Endpoint True

newtype Vert = Vert { toBools :: [Endpoint]}
  deriving (Eq , Ord )

instance Show Vert where
  show (Vert []) = ""
  show (Vert [e]) = show e
  show (Vert (e:es)) = show e ++ show (Vert es)

type Subst = Map Vert Vert

class Deg a where
  domdim :: a -> Int
  coddim :: a -> Int

instance Deg Subst where
  domdim = length . toBools . fst . head . Map.toList
  coddim = length . toBools . snd . head . Map.toList

-- instance Deg Tele where
--   domdim = undefined -- not possible to infer in general
--   coddim = length



-- Cubes

newtype Term = Term { term :: (Id , Tele)}

instance Show Term where
  show (Term (id , r)) = show id ++ " " ++ show r

newtype Point = Point { point :: Id }
  deriving (Eq)

emptT :: Id -> Term
emptT face = Term (face , Tele [])

idT :: Id -> Var -> Term
idT face i = Term (face , Tele [Formula [ Disj [Conj i]]])

newtype Type = Type { sides :: [(Term, Term)]}

instance Show Type where
  show (Type ss) = show ss

dim :: Type -> Int
dim = length . sides

newtype Decl = Decl { decl :: (Id , Type)}

instance Show Decl where
  show (Decl (id , ty)) = show id ++ " : " ++ show ty

newtype Cube = Cube { faces :: [Decl]}

instance Show Cube where
  show (Cube fc) = show fc


data Result = Dir Term | Comp Cube
