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

degSubst :: Subst
degSubst = Map.fromList [
              (Vert [e0] , Vert [e0])
            , (Vert [e1] , Vert [e0])
              ]

id2Subst :: Subst
id2Subst = Map.fromList [
              (Vert [e0, e0] , Vert [e0, e0])
            , (Vert [e0, e1] , Vert [e0, e1])
            , (Vert [e1, e0] , Vert [e1, e0])
            , (Vert [e1, e1] , Vert [e1, e1])
              ]

ddeg2Subst :: Subst
ddeg2Subst = Map.fromList [
              (Vert [e0, e0] , Vert [e0, e0])
            , (Vert [e0, e1] , Vert [e0, e0])
            , (Vert [e1, e0] , Vert [e0, e0])
            , (Vert [e1, e1] , Vert [e0, e0])
              ]
deg2Subst :: Subst
deg2Subst = Map.fromList [
              (Vert [e0, e0] , Vert [e0, e0])
            , (Vert [e0, e1] , Vert [e0, e0])
            , (Vert [e1, e0] , Vert [e0, e1])
            , (Vert [e1, e1] , Vert [e0, e1])
              ]
deg2Subst' :: Subst
deg2Subst' = Map.fromList [
              (Vert [e0, e0] , Vert [e0, e1])
            , (Vert [e0, e1] , Vert [e1, e1])
            , (Vert [e1, e0] , Vert [e1, e1])
            , (Vert [e1, e1] , Vert [e1, e1])
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

andOrSubst3 = Map.fromList [
              (Vert [e0, e0, e0] , Vert [e0, e0])
            , (Vert [e0, e0, e1] , Vert [e0, e1])
            , (Vert [e0, e1, e0] , Vert [e0, e1])
            , (Vert [e0, e1, e1] , Vert [e1, e1])
            , (Vert [e1, e0, e0] , Vert [e0, e1])
            , (Vert [e1, e0, e1] , Vert [e0, e1])
            , (Vert [e1, e1, e0] , Vert [e0, e1])
            , (Vert [e1, e1, e1] , Vert [e1, e1])
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
            , (Vert [e0, e1] , Vert [e0])
            , (Vert [e1, e0] , Vert [e1])
            , (Vert [e1, e1] , Vert [e1])
              ]


-- -- Constructor for a 1-path with single variable application
idT :: Id -> IVar -> Term
idT face i = Term face (tele2Subst (Tele [Formula [Disj [Conj i]]]) 1)

subst31 = Map.fromList [
              (Vert [e0 , e0, e0] , Vert [e0])
            , (Vert [e0 , e0, e1] , Vert [e1])
            , (Vert [e0 , e1, e0] , Vert [e1])
            , (Vert [e0 , e1, e1] , Vert [e1])
            , (Vert [e1 , e0, e0] , Vert [e1])
            , (Vert [e1 , e0, e1] , Vert [e1])
            , (Vert [e1 , e1, e0] , Vert [e1])
            , (Vert [e1 , e1, e1] , Vert [e1])
              ]

subst41 = Map.fromList [
              (Vert [e0 , e0 , e0, e0] , Vert [e0])
            , (Vert [e0 , e0 , e0, e1] , Vert [e0])
            , (Vert [e0 , e0 , e1, e0] , Vert [e1])
            , (Vert [e0 , e0 , e1, e1] , Vert [e1])
            , (Vert [e0 , e1 , e0, e0] , Vert [e0])
            , (Vert [e0 , e1 , e0, e1] , Vert [e0])
            , (Vert [e0 , e1 , e1, e0] , Vert [e1])
            , (Vert [e0 , e1 , e1, e1] , Vert [e1])
            , (Vert [e1 , e0 , e0, e0] , Vert [e0])
            , (Vert [e1 , e0 , e0, e1] , Vert [e0])
            , (Vert [e1 , e0 , e1, e0] , Vert [e1])
            , (Vert [e1 , e0 , e1, e1] , Vert [e1])
            , (Vert [e1 , e1 , e0, e0] , Vert [e0])
            , (Vert [e1 , e1 , e0, e1] , Vert [e0])
            , (Vert [e1 , e1 , e1, e0] , Vert [e1])
            , (Vert [e1 , e1 , e1, e1] , Vert [e1])
              ]

subst51 = Map.fromList [
              (Vert [e0 , e0 , e0 , e0, e0] , Vert [e0])
            , (Vert [e0 , e0 , e0 , e0, e1] , Vert [e0])
            , (Vert [e0 , e0 , e0 , e1, e0] , Vert [e0])
            , (Vert [e0 , e0 , e0 , e1, e1] , Vert [e0])
            , (Vert [e0 , e0 , e1 , e0, e0] , Vert [e0])
            , (Vert [e0 , e0 , e1 , e0, e1] , Vert [e0])
            , (Vert [e0 , e0 , e1 , e1, e0] , Vert [e0])
            , (Vert [e0 , e0 , e1 , e1, e1] , Vert [e0])
            , (Vert [e0 , e1 , e0 , e0, e0] , Vert [e0])
            , (Vert [e0 , e1 , e0 , e0, e1] , Vert [e0])
            , (Vert [e0 , e1 , e0 , e1, e0] , Vert [e0])
            , (Vert [e0 , e1 , e0 , e1, e1] , Vert [e0])
            , (Vert [e0 , e1 , e1 , e0, e0] , Vert [e0])
            , (Vert [e0 , e1 , e1 , e0, e1] , Vert [e0])
            , (Vert [e0 , e1 , e1 , e1, e0] , Vert [e0])
            , (Vert [e0 , e1 , e1 , e1, e1] , Vert [e0])
            , (Vert [e1 , e0 , e0 , e0, e0] , Vert [e0])
            , (Vert [e1 , e0 , e0 , e0, e1] , Vert [e0])
            , (Vert [e1 , e0 , e0 , e1, e0] , Vert [e0])
            , (Vert [e1 , e0 , e0 , e1, e1] , Vert [e0])
            , (Vert [e1 , e0 , e1 , e0, e0] , Vert [e1])
            , (Vert [e1 , e0 , e1 , e0, e1] , Vert [e1])
            , (Vert [e1 , e0 , e1 , e1, e0] , Vert [e1])
            , (Vert [e1 , e0 , e1 , e1, e1] , Vert [e1])
            , (Vert [e1 , e1 , e0 , e0, e0] , Vert [e0])
            , (Vert [e1 , e1 , e0 , e0, e1] , Vert [e0])
            , (Vert [e1 , e1 , e0 , e1, e0] , Vert [e0])
            , (Vert [e1 , e1 , e0 , e1, e1] , Vert [e0])
            , (Vert [e1 , e1 , e1 , e0, e0] , Vert [e1])
            , (Vert [e1 , e1 , e1 , e0, e1] , Vert [e1])
            , (Vert [e1 , e1 , e1 , e1, e0] , Vert [e1])
            , (Vert [e1 , e1 , e1 , e1, e1] , Vert [e1])
              ]



otherway :: PSubst
otherway = Map.fromList [
    (Vert [e0 , e0] , [Vert [e0 , e0]])
  , (Vert [e0 , e1] , [Vert [e0 , e0] , Vert [e0 , e1] , Vert [e1 , e0] , Vert [e1 , e1]])
  , (Vert [e1 , e0] , [Vert [e0 , e0] , Vert [e0 , e1] , Vert [e1 , e0] , Vert [e1 , e1]])
  , (Vert [e1 , e1] , [Vert [e0 , e0] , Vert [e0 , e1] , Vert [e1 , e0] , Vert [e1 , e1]])
                          ]




circle :: Cube
circle = Cube [
    Decl "a" (Boundary  [])
  , Decl "loop" (Boundary  [(Term "a" (constSubst 0) , Term "a" (constSubst 0))])
           ]

circle4 = inferBoundary circle (Term "loop" subst31)
circle5 = inferBoundary circle (Term "loop" subst41)
circle6 = inferBoundary circle (Term "loop" subst51)

circle5Cube = Boundary [
  (Term "a" (constSubst 4) , Term "a" (constSubst 4)) ,
  (Term "a" (constSubst 4) , Term "a" (constSubst 4)) ,
  (Term "a" (constSubst 4) , Term "a" (constSubst 4)) ,
  (Term "a" (constSubst 4) , Term "a" (constSubst 4)) ,
  (Term "loop" (tele2Subst (Tele [Formula [Disj [Conj 1]]]) 4) , Term "a" (constSubst 4))
  ]

int :: Cube
int = Cube [
    Decl "zero" (Boundary  [])
  , Decl "one" (Boundary  [])
  , Decl "seg" (Boundary  [(Term "zero" (constSubst 0) , Term "one" (constSubst 0))])
           ]

intApp1Term = Term "seg" $ tele2Subst (Tele [Formula [Disj [Conj 1]]]) 2
intApp1Boundary = Boundary [(Term "zero" (constSubst 1) , Term "one" (constSubst 1)) , (idT "seg" 1 , idT "seg" 1)]

intAnd2Term = Term "seg" $ tele2Subst (Tele [Formula [Disj [Conj 2]]]) 2
intApp2Boundary = Boundary [(Term "seg" app1Subst , Term "seg" app1Subst) , (Term "zero" (constSubst 1) , Term "one" (constSubst 1))]

intAndTerm = Term "seg" $ tele2Subst (Tele [Formula [Disj [Conj 1, Conj 2]]]) 2
intAndBoundary = Boundary [(Term "zero" (constSubst 1) , idT "seg" 1) , (Term "zero" (constSubst 2) , idT "seg" 1)]

intOrTerm = Term "seg" $ tele2Subst (Tele [Formula [Disj [Conj 1], Disj [Conj 2]]]) 2
intOrBoundary = Boundary [(Term "seg" app1Subst , Term "one" (constSubst 1)) , (Term "seg" app1Subst , Term "one" (constSubst 1))]

intInv :: Boundary
intInv = Boundary [(Term "one" (constSubst 0) , Term "zero" (constSubst 0))]





two :: Cube
two = Cube [
    Decl "a"     (Boundary [])
  , Decl "p"     (Boundary [(Term "a" (constSubst 0) , Term "a" (constSubst 0))])
  , Decl "q"     (Boundary [(Term "a" (constSubst 0) , Term "a" (constSubst 0))])
  , Decl "phi"   (Boundary [(Term "p" idSubst, Term "a" (constSubst 1)) , (Term "q" idSubst, Term "a" (constSubst 1)) ])
           ]

subst32 = Map.fromList [
              (Vert [e0 , e0, e0] , Vert [e0 , e0])
            , (Vert [e0 , e0, e1] , Vert [e0 , e1])
            , (Vert [e0 , e1, e0] , Vert [e0 , e0])
            , (Vert [e0 , e1, e1] , Vert [e0 , e1])
            , (Vert [e1 , e0, e0] , Vert [e0 , e1])
            , (Vert [e1 , e0, e1] , Vert [e1 , e1])
            , (Vert [e1 , e1, e0] , Vert [e0 , e1])
            , (Vert [e1 , e1, e1] , Vert [e1 , e1])
              ]





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
  -- , Decl "phi3"   (Boundary [(Term "f" app1Subst, Term "h" app1Subst) , (Term "phi" id2Subst , Term "phi" id2Subst) , (Term "x" (constSubst 2) , Term "g" app2Subst)])
           ]

triangleSlide :: Boundary
triangleSlide = Boundary [(Term "h" idSubst, Term "g" idSubst) , (Term "f" idSubst, Term "z" (constSubst 1))]

fgfgcube :: Boundary
fgfgcube = Boundary [
    (Term "f" app1Subst ,  Term "g" app1Subst)
  , (Term "f" app1Subst ,  Term "g" app1Subst)
  , (Term "phi" phisubst,  Term "phi" phisubst)
                    ]

  where phisubst = Map.fromList [
              (Vert [e0, e0] , Vert [e0, e0])
            , (Vert [e0, e1] , Vert [e1, e0])
            , (Vert [e1, e0] , Vert [e1, e0])
            , (Vert [e1, e1] , Vert [e1, e1])
              ]



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

asquare :: Boundary
asquare = Boundary [(Term "a" (constSubst 1), Term "a" (constSubst 1) ) , (Term "a" (constSubst 1), Term "a" (constSubst 1) )]

loopAndOr , loopAndOr' , loopSwap, loop4Cube , loop4Cube' :: Boundary
loopAndOr = Boundary [ (Term "p" andOrSubst , Term "a" (constSubst 2)) , (Term "a" (constSubst 2) , Term "a" (constSubst 2)) , (Term "a" (constSubst 2) , Term "a" (constSubst 2)) ]

loopAndOr' = Boundary [ (Term "a" (constSubst 2) , Term "a" (constSubst 2)) , (Term "a" (constSubst 2) , Term "a" (constSubst 2)) ,(Term "p" andOrSubst , Term "a" (constSubst 2))  ]

loopSwap = Boundary [ (Term "p" (tele2Subst (Tele [Formula [Disj [Conj 1]] , Formula [Disj [Conj 2]]]) 2), Term "p" (tele2Subst swap 2)) , (Term "a" (constSubst 2) , Term "a" (constSubst 2)) , (Term "a" (constSubst 2) , Term "a" (constSubst 2)) ]


loop4Cube = Boundary [ (Term "p" (tele2Subst (Tele [Formula [Disj [Conj 1, Conj 2 , Conj 3]] , Formula [Disj [Conj 1], Disj [Conj 2] , Disj [Conj 3]]]) 3) , Term "a" (constSubst 3)) , (Term "a" (constSubst 3) , Term "a" (constSubst 3)) , (Term "a" (constSubst 3) , Term "a" (constSubst 3)) , (Term "a" (constSubst 3) , Term "a" (constSubst 3)) ]

loop4Cube' = Boundary [ (Term "a" (constSubst 3) , Term "a" (constSubst 3)) , (Term "p" (tele2Subst (Tele [Formula [Disj [Conj 1, Conj 2 , Conj 3]] , Formula [Disj [Conj 1], Disj [Conj 2] , Disj [Conj 3]]]) 3) , Term "a" (constSubst 3)) , (Term "a" (constSubst 3) , Term "a" (constSubst 3)) , (Term "a" (constSubst 3) , Term "a" (constSubst 3))  ]

loop4Cube'' = Boundary [ (Term "a" (constSubst 3) , Term "a" (constSubst 3)) , (Term "a" (constSubst 3) , Term "a" (constSubst 3)) , (Term "a" (constSubst 3) , Term "a" (constSubst 3)) , (Term "p" (tele2Subst (Tele [Formula [Disj [Conj 1, Conj 2 , Conj 3]] , Formula [Disj [Conj 1], Disj [Conj 2] , Disj [Conj 3]]]) 3) , Term "a" (constSubst 3))   ]

loop5Cube = Boundary [ (Term "p" (tele2Subst (Tele [Formula [Disj [Conj 1, Conj 2 , Conj 3 , Conj 4]] , Formula [Disj [Conj 1], Disj [Conj 2] , Disj [Conj 3] , Disj [Conj 4]]]) 4) , Term "a" (constSubst 4)) , (Term "a" (constSubst 4) , Term "a" (constSubst 4)) , (Term "a" (constSubst 4) , Term "a" (constSubst 4)) , (Term "a" (constSubst 4) , Term "a" (constSubst 4)) ,  (Term "a" (constSubst 4) , Term "a" (constSubst 4)) ]

loop5Cube' = Boundary [
  (Term "a" (constSubst 4) , Term "a" (constSubst 4)) ,
  (Term "p" (tele2Subst (Tele [Formula [Disj [Conj 1, Conj 2 , Conj 3 , Conj 4]] , Formula [Disj [Conj 1], Disj [Conj 2] , Disj [Conj 3] , Disj [Conj 4]]]) 4) , Term "a" (constSubst 4)) ,
  (Term "a" (constSubst 4) , Term "a" (constSubst 4)) ,
  (Term "a" (constSubst 4) , Term "a" (constSubst 4)) ,
  (Term "a" (constSubst 4) , Term "a" (constSubst 4))
  ]

loop5Cube'' = Boundary [
  (Term "a" (constSubst 4) , Term "a" (constSubst 4)) ,
  (Term "a" (constSubst 4) , Term "a" (constSubst 4)) ,
  (Term "a" (constSubst 4) , Term "a" (constSubst 4)) ,
  (Term "a" (constSubst 4) , Term "a" (constSubst 4)) ,
  (Term "p" (tele2Subst (Tele [Formula [Disj [Conj 1, Conj 2 , Conj 3 , Conj 4]] , Formula [Disj [Conj 1], Disj [Conj 2] , Disj [Conj 3] , Disj [Conj 4]]]) 4) , Term "a" (constSubst 4))
  ]

loop6Cube = Boundary [
  (Term "p" (tele2Subst (Tele [Formula [Disj [Conj 1, Conj 2 , Conj 3 , Conj 4 , Conj 5]] , Formula [Disj [Conj 1], Disj [Conj 2] , Disj [Conj 3] , Disj [Conj 4] , Disj [Conj 5]]]) 5) , Term "a" (constSubst 5)) ,
  (Term "a" (constSubst 5) , Term "a" (constSubst 5)) ,
  (Term "a" (constSubst 5) , Term "a" (constSubst 5)) ,
  (Term "a" (constSubst 5) , Term "a" (constSubst 5)) ,
  (Term "a" (constSubst 5) , Term "a" (constSubst 5)) ,
  (Term "a" (constSubst 5) , Term "a" (constSubst 5))
  ]

loop6Cube' = Boundary [
  (Term "a" (constSubst 5) , Term "a" (constSubst 5)) ,
  (Term "p" (tele2Subst (Tele [Formula [Disj [Conj 1, Conj 2 , Conj 3 , Conj 4 , Conj 5]] , Formula [Disj [Conj 1], Disj [Conj 2] , Disj [Conj 3] , Disj [Conj 4] , Disj [Conj 5]]]) 5) , Term "a" (constSubst 5)) ,
  (Term "a" (constSubst 5) , Term "a" (constSubst 5)) ,
  (Term "a" (constSubst 5) , Term "a" (constSubst 5)) ,
  (Term "a" (constSubst 5) , Term "a" (constSubst 5)) ,
  (Term "a" (constSubst 5) , Term "a" (constSubst 5))
  ]

loop7Cube = Boundary [
  (Term "a" (constSubst 6) , Term "a" (constSubst 6)) ,
  (Term "a" (constSubst 6) , Term "a" (constSubst 6)) ,
  (Term "a" (constSubst 6) , Term "a" (constSubst 6)) ,
  (Term "a" (constSubst 6) , Term "a" (constSubst 6)) ,
  (Term "a" (constSubst 6) , Term "a" (constSubst 6)) ,
  (Term "a" (constSubst 6) , Term "a" (constSubst 6)) ,
  (Term "p" (tele2Subst (Tele [Formula [Disj [Conj 1, Conj 2 , Conj 3 , Conj 4 , Conj 5 , Conj 6]] , Formula [Disj [Conj 1], Disj [Conj 2] , Disj [Conj 3] , Disj [Conj 4] , Disj [Conj 5] , Disj [Conj 6]]]) 6) , Term "a" (constSubst 6)) 
  ]


-- z2 :: Cube
-- z2 = Cube [
--     Decl "o"     (Boundary [])
--   , Decl "p"     (Boundary [(Term "o" (constSubst 0) , Term "o" (constSubst 0))])
--   , Decl "q"     (Boundary [(Term "o" (constSubst 0) , Term "o" (constSubst 0))])
--   , Decl "r"     (Boundary [(Term "o" (constSubst 0) , Term "o" (constSubst 0))])
--   , Decl "law"   (Boundary [(Term "p" idSubst , Term "o" (constSubst 1)) , (Term "q" idSubst , Term "r" idSubst)])
--                    ]

z2 :: Cube
z2 = Cube [
    Decl "o"     (Boundary [])
  , Decl "a"     (Boundary [(Term "o" (constSubst 0) , Term "o" (constSubst 0))])
  , Decl "b"     (Boundary [(Term "o" (constSubst 0) , Term "o" (constSubst 0))])
  , Decl "law"   (Boundary [(Term "a" idSubst , Term "a" idSubst) , (Term "b" idSubst , Term "b" idSubst)])
                   ]

inv :: Id -> Id -> Id -> Term
inv i0 i1 p = Comp (Box [(Term p idSubst , Term i1 (constSubst 0))] (Term i0 (constSubst 0)) )


z2goal :: Boundary
z2goal = Boundary [ (inv "o" "o" "b" , inv "o" "o" "b") , (Term "a" idSubst , Term "a" idSubst) ]


binom n k = product [1+n-k..n] `div` product [1..k]

d :: Int -> Int
d 0 = 2
d 1 = 3
d 2 = 6
d 3 = 20
-- d 4 = 20 + 19 + 3 * 14 + 3 * 11 + 9 + 3 * 6 + 3 * 5 + 3 * 3 + 2 + 1
d 4 = d 3 -- all 0
      + (d 3 - (d 0 - 1)) -- a =  19
      + 3 * (d 2 * (d 1)) -- b = 14
      + 3 * (d 3 - (d 2 + d 1)) -- c = 11
      + 3 + 3 + 3 -- (d 3 - (3 * (d 1 - 1) + 3 * (2 * (d 1 - 1)))) -- d = 9
      + 3 * d 2 -- e = 6
      + 3 * (d 2 - 1) -- f = 5
      + 3 * d 1 -- 3 * (d 3 - 0) --  g = 3
      + (d 0)-- h = 2
      + 1 -- all 1
-- d 5 = 1
--       + 4 + binom 4 2 + binom 4 3 + 1
--       + 6 * (binom 3 0 + binom 3 1 + binom 3 2 + binom 3 0)
--       + (binom 6 2) * 

d 5 = d 4 -- all 0
      + (d 4 - (d 0 - 1)) -- a = 167
      + binom 4 1 * (d 4 - d 3) -- 148
      + binom 4 2 * (d 4 - (d 3 + (d 3 - d 2))) -- 134
      + binom 4 3 * (d 3 * d 2 + d 1) -- 123
      + binom 4 4 * (6 * (d 2 + d 1)) -- 114
      + binom 6 1 * (d 3 * 4 - d 2) -- 84
      + binom 6 1 * binom 2 1 * (78) -- 78
      + binom 6 2 * (53) -- 53
      + binom 6 2 * binom 1 1 * (50) -- 50
      + binom 6 3 * (36) -- 36
      + binom 6 4 * (27) -- 27
      + binom 6 5 * (21) -- 21
      + binom 6 6 * (17) -- 17
      + 3 * d 2 -- e = 6
      + 3 * (d 2 - 1) -- f = 5
      + 3 * d 1 -- 3 * (d 3 - 0) --  g = 3
      + (d 0)-- h = 2
      + 1 -- all 1


psubst3 = Map.fromList [
              (Vert [e0, e0, e0] , [Vert [e0] , Vert [e1]])
            , (Vert [e0, e0, e1] , [Vert [e1]])
            , (Vert [e0, e1, e0] , [Vert [e0] , Vert [e1]])
            , (Vert [e1, e0, e0] , [Vert [e0] , Vert [e1]])
            , (Vert [e0, e1, e1] , [Vert [e1]])
            , (Vert [e1, e0, e1] , [Vert [e1]])
            , (Vert [e1, e1, e0] , [Vert [e1]])
            , (Vert [e1, e1, e1] , [Vert [e1]])
              ]

psubst4 = Map.fromList [
              (Vert [e0, e0, e0, e0] , [Vert [e0] , Vert [e1]])
            , (Vert [e0, e0, e0, e1] , [Vert [e0] , Vert [e1]])
            , (Vert [e0, e0, e1, e0] , [Vert [e0] , Vert [e1]])
            , (Vert [e0, e1, e0, e0] , [Vert [e0] , Vert [e1]])
            , (Vert [e0, e0, e1, e1] , [Vert [e1]])
            , (Vert [e0, e1, e0, e1] , [Vert [e1]])
            , (Vert [e0, e1, e1, e0] , [Vert [e1]])
            , (Vert [e0, e1, e1, e1] , [Vert [e1]])
            , (Vert [e1, e0, e0, e0] , [Vert [e0] , Vert [e1]])
            , (Vert [e1, e0, e0, e1] , [Vert [e1]])
            , (Vert [e1, e0, e1, e0] , [Vert [e1]])
            , (Vert [e1, e1, e0, e0] , [Vert [e1]])
            , (Vert [e1, e0, e1, e1] , [Vert [e1]])
            , (Vert [e1, e1, e0, e1] , [Vert [e1]])
            , (Vert [e1, e1, e1, e0] , [Vert [e1]])
            , (Vert [e1, e1, e1, e1] , [Vert [e1]])
              ]
