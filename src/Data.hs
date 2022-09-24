{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Data where

import Data.List
import qualified Data.Map as Map
import Data.Map ((!), Map)

import Prel


-- Formulas

type IVar = Int
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


vdiff :: Vert -> Vert -> Int
vdiff (Vert []) (Vert []) = 0
vdiff (Vert (e:es)) (Vert (e':es')) = (if e == e' then 0 else 1) + vdiff (Vert es) (Vert es')

getPath :: Vert -> Vert -> (IVar , Endpoint)
getPath (Vert (e:es)) (Vert (e':es')) =
  if e == e'
    then (1 , e)
    else let (i , e'') = getPath (Vert es) (Vert es') in (i + 1 , e'')

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

data Term = Term Id Tele | Comp Box
  deriving (Eq , Show)

data Box = Box [(Term , Term)] Term
  deriving (Eq , Show)


-- instance Show Term where
--   show (Term id r) = show id ++ " " ++ show r
--   show (Comp b) = show b -- show sides ++ " " ++ show back

newtype Point = Point { point :: Id }
  deriving (Eq , Show)

emptT :: Id -> Term
emptT face = Term face (Tele [])

idT :: Id -> IVar -> Term
idT face i = Term face (Tele [Formula [ Disj [Conj i]]])

newtype Type = Type { faces :: [(Term, Term)]}

instance Show Type where
  show (Type ss) = show ss

dim :: Type -> Int
dim = length . faces

newtype Decl = Decl { decl :: (Id , Type)}

instance Show Decl where
  show (Decl (id , ty)) = show id ++ " : " ++ show ty

newtype Cube = Cube { constr :: [Decl]}

instance Show Cube where
  show (Cube fc) = show fc

