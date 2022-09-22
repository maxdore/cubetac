module Examples where

import Data.List
import qualified Data.Map as Map
import Data.Map ((!), Map)

import Prel
import Data
import Deg
import Type


orSubst , andSubst :: Subst
orSubst = Map.fromList [
              (Vert [e0, e0] , Vert [e0])
            , (Vert [e0, e1] , Vert [e1])
            , (Vert [e1, e0] , Vert [e1])
            , (Vert [e1, e1] , Vert [e1])
              ]
andSubst = Map.fromList [
              (Vert [e0, e0] , Vert [e0])
            , (Vert [e0, e1] , Vert [e0])
            , (Vert [e1, e0] , Vert [e0])
            , (Vert [e1, e1] , Vert [e1])
              ]

bothSubst = Map.fromList [
              (Vert [e0, e0, e0] , Vert [e0])
            , (Vert [e0, e0, e1] , Vert [e0])
            , (Vert [e0, e1, e0] , Vert [e0])
            , (Vert [e0, e1, e1] , Vert [e0])
            , (Vert [e1, e0, e0] , Vert [e0])
            , (Vert [e1, e0, e1] , Vert [e1])
            , (Vert [e1, e1, e0] , Vert [e1])
            , (Vert [e1, e1, e1] , Vert [e1])
              ]

andOrSubst = Map.fromList [
              (Vert [e0, e0] , Vert [e0, e0])
            , (Vert [e0, e1] , Vert [e0, e1])
            , (Vert [e1, e0] , Vert [e0, e1])
            , (Vert [e1, e1] , Vert [e1, e1])
              ]

idTele , id2Tele , orTele , andTele :: Tele
idTele = Tele [Formula [Disj [Conj 1]]]
id2Tele = Tele [Formula [Disj [Conj 2]]]
orTele = Tele [Formula [Disj [Conj 1], Disj [Conj 2]]]
andTele = Tele [Formula [Disj [Conj 1, Conj 2]]]
bothTele = Tele [Formula [Disj [Conj 1, Conj 2] , Disj [Conj 1 , Conj 3]]]
andOrTele = Tele [Formula [Disj [Conj 1, Conj 2]] , Formula [Disj [Conj 1], Disj [Conj 2]]]



int :: Cube
int = Cube [
    Decl ("zero" ,   Type  [])
  , Decl ("one" ,    Type  [])
  , Decl ("seg" ,    Type  [(emptT "zero" , emptT "one")])
           ]

intApp1Term = Term ("seg" , Tele [Formula [Disj [Conj 1]]])
intApp1Type = Type [(emptT "zero" , emptT "one") , (idT "seg" 1 , idT "seg" 1)]

intAnd2Term = Term ("seg" , Tele [Formula [Disj [Conj 2]]])
intApp2Type = Type [(idT "seg" 1 , idT "seg" 1) , (emptT "zero" , emptT "one")]

intAndTerm = Term ("seg" , Tele [Formula [Disj [Conj 1, Conj 2]]])
intAndType = Type [(emptT "zero" , idT "seg" 1) , (emptT "zero" , idT "seg" 1)]

intOrTerm = Term ("seg" , Tele [Formula [Disj [Conj 1], Disj [Conj 2]]])
intOrType = Type [(idT "seg" 1 , emptT "one") , (idT "seg" 1 , emptT "one")]

intInv :: Type
intInv = Type [(emptT "one" , emptT "zero")]

triangle :: Cube
triangle = Cube [
    Decl ("x" ,     Type [])
  , Decl ("y" ,     Type [])
  , Decl ("z" ,     Type [])
  , Decl ("f" ,     Type [(emptT "x" , emptT "y")])
  , Decl ("g" ,     Type [(emptT "y" , emptT "z")])
  , Decl ("h" ,     Type [(emptT "x" , emptT "z")])
  , Decl ("phi" ,   Type [(idT "f" 1, idT "h" 1) , (emptT "x" , idT "g" 1)])
           ]



triangleSlide :: Type
triangleSlide = Type [(idT "h" 1, idT "g" 1) , (idT "f" 1, emptT "z")]

