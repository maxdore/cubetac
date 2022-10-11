module Examples where

import Data.List
import qualified Data.Map as Map
import Data.Map ((!), Map)

import Prel
import Data
import Poset
import Formula

idSubst :: Subst
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
redSubst = Map.fromList [
              (Vert [e0, e0] , Vert [e0])
            , (Vert [e0, e1] , Vert [e0])
            , (Vert [e1, e0] , Vert [e1])
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
    Decl "zero" (Boundary  [])
  , Decl "one" (Boundary  [])
  , Decl "seg" (Boundary  [(Term "zero" (constSubst 2) , Term "one" (constSubst 2))])
           ]

intApp1Term = Term "seg" $ tele2Subst (Tele [Formula [Disj [Conj 1]]]) 2
intApp1Boundary = Boundary [(Term "zero" (constSubst 2) , Term "one" (constSubst 2)) , (idT "seg" 1 , idT "seg" 1)]

intAnd2Term = Term "seg" $ tele2Subst (Tele [Formula [Disj [Conj 2]]]) 2
intApp2Boundary = Boundary [(Term "seg" app1Subst , Term "seg" app1Subst) , (Term "zero" (constSubst 2) , Term "one" (constSubst 2))]

intAndTerm = Term "seg" $ tele2Subst (Tele [Formula [Disj [Conj 1, Conj 2]]]) 2
intAndBoundary = Boundary [(Term "zero" (constSubst 2) , idT "seg" 1) , (Term "zero" (constSubst 2) , idT "seg" 1)]

intOrTerm = Term "seg" $ tele2Subst (Tele [Formula [Disj [Conj 1], Disj [Conj 2]]]) 2
intOrBoundary = Boundary [(Term "seg" app1Subst , Term "one" (constSubst 2)) , (Term "seg" app1Subst , Term "one" (constSubst 2))]

intInv :: Boundary
intInv = Boundary [(Term "one" (constSubst 2) , Term "zero" (constSubst 2))]




twopaths :: Cube
twopaths = Cube [
    Decl "x"     (Boundary [])
  , Decl "y"     (Boundary [])
  , Decl "z"     (Boundary [])
  , Decl "f"     (Boundary [(Term "x" (constSubst 0) , Term "y" (constSubst 0))])
  , Decl "g"     (Boundary [(Term "y" (constSubst 0) , Term "z" (constSubst 0))])
           ]

fgfg :: Boundary
fgfg = Boundary [(Term "f" idSubst, Term "g" idSubst) , (Term "f" idSubst, Term "g" idSubst)]



triangle :: Cube
triangle = Cube [
    Decl "x"     (Boundary [])
  , Decl "y"     (Boundary [])
  , Decl "z"     (Boundary [])
  , Decl "f"     (Boundary [(Term "x" (constSubst 0) , Term "y" (constSubst 0))])
  , Decl "g"     (Boundary [(Term "y" (constSubst 0) , Term "z" (constSubst 0))])
  , Decl "h"     (Boundary [(Term "x" (constSubst 0) , Term "z" (constSubst 0))])
  , Decl "phi"   (Boundary [(Term "f" idSubst, Term "h" idSubst) , (Term "x" (constSubst 1) , Term "g" idSubst)])
           ]

triangleSlide :: Boundary
triangleSlide = Boundary [(Term "h" idSubst, Term "g" idSubst) , (Term "f" idSubst, Term "z" (constSubst 1))]



composition :: Cube
composition = Cube [
    Decl "x"     (Boundary [])
  , Decl "y"     (Boundary [])
  , Decl "z"     (Boundary [])
  , Decl "w"     (Boundary [])
  , Decl "p"     (Boundary [(Term "x" (constSubst 1) , Term "y" (constSubst 1))])
  , Decl "q"     (Boundary [(Term "y" (constSubst 1) , Term "z" (constSubst 1))])
  , Decl "r"     (Boundary [(Term "z" (constSubst 1) , Term "w" (constSubst 1))])
                   ]

compfiller :: Boundary
compfiller = Boundary [(Term "p" app1Subst, Comp (Box [(Term "x" (constSubst 1) , Term "q" app1Subst)] (idT "p" 1))) , (Term "x" (constSubst 2) , Term "q" app1Subst)]

compassoc :: Boundary
compassoc = Boundary [(undefined , undefined) , (Term "x" (constSubst 2) , Term "w" (constSubst 2))]



loopspace :: Cube
loopspace = Cube [
    Decl "a"   (Boundary [])
  , Decl "p"   (Boundary [(Term "a" (constSubst 1) , Term "a" (constSubst 1)) , (Term "a" (constSubst 1) , Term "a" (constSubst 1))])
                 ]

loopAndOr , loopAndOr' , loop4Cube , loop4Cube' :: Boundary
loopAndOr = Boundary [ (Term "p" andOrSubst , Term "a" (constSubst 2)) , (Term "a" (constSubst 2) , Term "a" (constSubst 2)) , (Term "a" (constSubst 2) , Term "a" (constSubst 2)) ]

loopAndOr' = Boundary [ (Term "a" (constSubst 2) , Term "a" (constSubst 2)) , (Term "a" (constSubst 2) , Term "a" (constSubst 2)) ,(Term "p" andOrSubst , Term "a" (constSubst 2))  ]

loop4Cube = Boundary [ (Term "p" (tele2Subst (Tele [Formula [Disj [Conj 1, Conj 2 , Conj 3]] , Formula [Disj [Conj 1], Disj [Conj 2] , Disj [Conj 3]]]) 3) , Term "a" (constSubst 3)) , (Term "a" (constSubst 3) , Term "a" (constSubst 3)) , (Term "a" (constSubst 3) , Term "a" (constSubst 3)) , (Term "a" (constSubst 3) , Term "a" (constSubst 3)) ]

loop4Cube' = Boundary [ (Term "a" (constSubst 3) , Term "a" (constSubst 3)) , (Term "p" (tele2Subst (Tele [Formula [Disj [Conj 1, Conj 2 , Conj 3]] , Formula [Disj [Conj 1], Disj [Conj 2] , Disj [Conj 3]]]) 3) , Term "a" (constSubst 3)) , (Term "a" (constSubst 3) , Term "a" (constSubst 3)) , (Term "a" (constSubst 3) , Term "a" (constSubst 3))  ]
