module Examples where

import Data.List
import qualified Data.Map as Map
import Data.Map ((!), Map)

import Prel
import Data
import Poset
import Formula

idSubst = Map.fromList [
              (Vert [e0] , Vert [e0])
            , (Vert [e1] , Vert [e1])
              ]

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


stretch = Map.fromList [
              (Vert [e0, e0] , Vert [e0, e0])
            , (Vert [e0, e1] , Vert [e0, e1])
            , (Vert [e1, e0] , Vert [e1, e1])
            , (Vert [e1, e1] , Vert [e1, e1])
              ]


idTele , id2Tele , orTele , andTele :: Tele
idTele = Tele [Formula [Disj [Conj 1]]]
id2Tele = Tele [Formula [Disj [Conj 2]]]
orTele = Tele [Formula [Disj [Conj 1], Disj [Conj 2]]]
andTele = Tele [Formula [Disj [Conj 1, Conj 2]]]
bothTele = Tele [Formula [Disj [Conj 1, Conj 2] , Disj [Conj 1 , Conj 3]]]
andOrTele = Tele [Formula [Disj [Conj 1, Conj 2]] , Formula [Disj [Conj 1], Disj [Conj 2]]]
swap = Tele [Formula [Disj [Conj 2]] , Formula [Disj [Conj 1]]]

app1Subst = Map.fromList [
              (Vert [e0, e0] , Vert [e0])
            , (Vert [e0, e1] , Vert [e1])
            , (Vert [e1, e0] , Vert [e0])
            , (Vert [e1, e1] , Vert [e1])
              ]

app2Subst = Map.fromList [
              (Vert [e0, e0] , Vert [e0])
            , (Vert [e0, e1] , Vert [e1])
            , (Vert [e1, e0] , Vert [e0])
            , (Vert [e1, e1] , Vert [e1])
              ]


-- -- Constructor for a 1-path with single variable application
idT :: Id -> IVar -> Term
idT face i = Term face undefined


int :: Cube
int = Cube [
    Decl "zero" (Type  [])
  , Decl "one" (Type  [])
  , Decl "seg" (Type  [(Term "zero" (constSubst 2) , Term "one" (constSubst 2))])
           ]

intApp1Term = Term "seg" $ tele2Subst (Tele [Formula [Disj [Conj 1]]]) 2
intApp1Type = Type [(Term "zero" (constSubst 2) , Term "one" (constSubst 2)) , (idT "seg" 1 , idT "seg" 1)]

intAnd2Term = Term "seg" $ tele2Subst (Tele [Formula [Disj [Conj 2]]]) 2
intApp2Type = Type [(Term "seg" app1Subst , Term "seg" app1Subst) , (Term "zero" (constSubst 2) , Term "one" (constSubst 2))]

intAndTerm = Term "seg" $ tele2Subst (Tele [Formula [Disj [Conj 1, Conj 2]]]) 2
intAndType = Type [(Term "zero" (constSubst 2) , idT "seg" 1) , (Term "zero" (constSubst 2) , idT "seg" 1)]

intOrTerm = Term "seg" $ tele2Subst (Tele [Formula [Disj [Conj 1], Disj [Conj 2]]]) 2
intOrType = Type [(Term "seg" app1Subst , Term "one" (constSubst 2)) , (Term "seg" app1Subst , Term "one" (constSubst 2))]

intInv :: Type
intInv = Type [(Term "one" (constSubst 2) , Term "zero" (constSubst 2))]




twopaths :: Cube
twopaths = Cube [
    Decl "x"     (Type [])
  , Decl "y"     (Type [])
  , Decl "z"     (Type [])
  , Decl "f"     (Type [(Term "x" (constSubst 0) , Term "y" (constSubst 0))])
  , Decl "g"     (Type [(Term "y" (constSubst 0) , Term "z" (constSubst 0))])
           ]

fgfg :: Type
fgfg = Type [(Term "f" idSubst, Term "g" idSubst) , (Term "f" idSubst, Term "g" idSubst)]



triangle :: Cube
triangle = Cube [
    Decl "x"     (Type [])
  , Decl "y"     (Type [])
  , Decl "z"     (Type [])
  , Decl "f"     (Type [(Term "x" (constSubst 0) , Term "y" (constSubst 0))])
  , Decl "g"     (Type [(Term "y" (constSubst 0) , Term "z" (constSubst 0))])
  , Decl "h"     (Type [(Term "x" (constSubst 0) , Term "z" (constSubst 0))])
  , Decl "phi"   (Type [(Term "f" idSubst, Term "h" idSubst) , (Term "x" (constSubst 1) , Term "g" idSubst)])
           ]

triangleSlide :: Type
triangleSlide = Type [(Term "h" app1Subst, Term "g" app1Subst) , (Term "f" app1Subst, Term "z" (constSubst 2))]



composition :: Cube
composition = Cube [
    Decl "x"     (Type [])
  , Decl "y"     (Type [])
  , Decl "z"     (Type [])
  , Decl "w"     (Type [])
  , Decl "p"     (Type [(Term "x" (constSubst 1) , Term "y" (constSubst 1))])
  , Decl "q"     (Type [(Term "y" (constSubst 1) , Term "z" (constSubst 1))])
  , Decl "r"     (Type [(Term "z" (constSubst 1) , Term "w" (constSubst 1))])
                   ]

compfiller :: Type
compfiller = Type [(Term "p" app1Subst, Comp (Box [(Term "x" (constSubst 1) , Term "q" app1Subst)] (idT "p" 1))) , (Term "x" (constSubst 2) , Term "q" app1Subst)]

compassoc :: Type
compassoc = Type [(undefined , undefined) , (Term "x" (constSubst 2) , Term "w" (constSubst 2))]


-- TODO with more paths to build
      -- ________
      -- |      |
      -- |      |
      -- - - - -
      -- |      |
      -- |      |
      -- - - - -


loopspace :: Cube
loopspace = Cube [
    Decl "a"   (Type [])
  , Decl "p"   (Type [(Term "a" (constSubst 2) , Term "a" (constSubst 2)) , (Term "a" (constSubst 2) , Term "a" (constSubst 2))])
                 ]

loopAndOr :: Type
loopAndOr = Type [ (Term "p" andOrSubst , Term "a" (constSubst 2)) , (Term "a" (constSubst 2) , Term "a" (constSubst 2)) , (Term "a" (constSubst 2) , Term "a" (constSubst 2)) ]
