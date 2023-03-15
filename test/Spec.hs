import Data.List
import qualified Data.Map as Map
import Data.Map ((!), Map)

import Prel
import Poset
import Data
import Formula
import ContortionSolver
import CompositionSolver
import Solver


idSubst :: Subst
idSubst = Map.fromList [
              (Vert [e0] , Vert [e0])
            , (Vert [e1] , Vert [e1])
              ]

id2Subst :: Subst
id2Subst = Map.fromList [
              (Vert [e0, e0] , Vert [e0, e0])
            , (Vert [e0, e1] , Vert [e0, e1])
            , (Vert [e1, e0] , Vert [e1, e0])
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
app1Subst = Map.fromList [
              (Vert [e0, e0] , Vert [e0])
            , (Vert [e0, e1] , Vert [e0])
            , (Vert [e1, e0] , Vert [e1])
            , (Vert [e1, e1] , Vert [e1])
              ]

app2Subst = Map.fromList [
              (Vert [e0, e0] , Vert [e0])
            , (Vert [e0, e1] , Vert [e1])
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



int :: Cube
int = Cube [
    Decl "zero" (Boundary  [])
  , Decl "one" (Boundary  [])
  , Decl "seg" (Boundary  [(Term "zero" (constSubst 0) , Term "one" (constSubst 0))])
           ]



twopaths :: Cube
twopaths = Cube [
    Decl "x"     (Boundary [])
  , Decl "y"     (Boundary [])
  , Decl "z"     (Boundary [])
  , Decl "f"     (Boundary [(Term "x" (constSubst 0) , Term "y" (constSubst 0))])
  , Decl "g"     (Boundary [(Term "y" (constSubst 0) , Term "z" (constSubst 0))])
           ]


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

z2 :: Cube
z2 = Cube [
    Decl "o"     (Boundary [])
  , Decl "a"     (Boundary [(Term "o" (constSubst 0) , Term "o" (constSubst 0))])
  , Decl "law"   (Boundary [(Term "a" idSubst , Term "o" (constSubst 1)) , (Term "o" (constSubst 1) , Term "a" idSubst)])
                   ]

gp :: Cube
gp = Cube [
    Decl "o"     (Boundary [])
  , Decl "a"     (Boundary [(Term "o" (constSubst 0) , Term "o" (constSubst 0))])
  , Decl "b"     (Boundary [(Term "o" (constSubst 0) , Term "o" (constSubst 0))])
  , Decl "law"   (Boundary [(Term "a" idSubst , Term "a" idSubst) , (Term "b" idSubst , Term "b" idSubst)])
                   ]

inv :: Id -> Id -> Id -> Box
inv i0 i1 p = (Box [(Term p idSubst , Term i1 (constSubst 1))] (Term i0 (constSubst 1)) )

comp :: Id -> Term -> Term -> Box
comp x p q = Box [(Term x (constSubst 1) , q)] p

loopspace :: Cube
loopspace = Cube [
    Decl "a"   (Boundary [])
  , Decl "p"   (Boundary [(Term "a" (constSubst 1) , Term "a" (constSubst 1)) , (Term "a" (constSubst 1) , Term "a" (constSubst 1))])
                 ]


checkNormalize :: Cube -> Term -> Term -> IO()
checkNormalize ctxt p q = putStrLn $
  let infq = normalize ctxt p in
  if infq == q then "OK" else "FAIL! " ++ show p ++ " normal form given and normalized term do not match:\n" ++ show q ++ "\n" ++ show infq

checkTermBoundary :: Cube -> Term -> Boundary -> IO()
checkTermBoundary ctxt p ty = putStrLn $
  let infty = inferBoundary ctxt p in
  if infty == ty then "OK" else "FAIL! " ++ show p ++ " given type and inferred type do not match:\n" ++ show ty ++ "\n" ++ show infty

checkFindContortion :: Cube -> Boundary -> Term -> IO()
checkFindContortion ctxt ty p = putStrLn $
  case findContortion ctxt ty of
    Nothing -> "FAIL! No solution found for " ++ show ty
    Just infp -> if infp == p then "OK" else "FAIL! " ++ show ty ++ " given and found solution do not match:\n" ++ show p ++ "\n" ++ show infp


checkSolve :: Cube -> Boundary -> Term -> IO()
checkSolve ctxt ty p = putStrLn $
  case solve ctxt ty of
    Nothing -> "FAIL! No solution found for " ++ show ty
    Just infp -> if infp == p then "OK" else "FAIL! " ++ show ty ++ " given and found solution do not match:\n" ++ show p ++ "\n" ++ show infp

main :: IO ()
main = do
  checkNormalize int
    (Term "zero" (constSubst 1))
    (Term "zero" (constSubst 1))

  checkNormalize int
    (Term "seg" (Map.fromList [
              (Vert [e0] , Vert [e0])
            , (Vert [e1] , Vert [e1])
              ]))
    (Term "seg" (Map.fromList [
              (Vert [e0] , Vert [e0])
            , (Vert [e1] , Vert [e1])
              ]))

  checkNormalize int
    (Term "seg" (Map.fromList [
              (Vert [e0] , Vert [e0])
            , (Vert [e1] , Vert [e0])
              ]))
    (Term "zero" (constSubst 1))

  checkNormalize loopspace
    (Term "p" andOrSubst)
    (Term "p" andOrSubst)

  checkNormalize loopspace
    (Term "p" (Map.fromList [
              (Vert [e0, e0] , Vert [e0, e0])
            , (Vert [e0, e1] , Vert [e0, e1])
            , (Vert [e1, e0] , Vert [e0, e0])
            , (Vert [e1, e1] , Vert [e0, e1])
              ]))
    (Term "a" (constSubst 2))

  checkNormalize int
    (Term "zero" $ Map.fromList [(Vert[], Vert[])])
    (Term "zero" (constSubst 0))

  checkNormalize int
    (Term "seg" $ Map.fromList [(Vert[], Vert[e0])])
    (Term "zero" (constSubst 0))

  checkTermBoundary int
    (Term "seg" $ tele2Subst (Tele [Formula [Disj [Conj 1]]]) 2)
    (Boundary [(Term "zero" (constSubst 1), Term "one" (constSubst 1)),(Term "seg" idSubst, Term "seg" idSubst) ])

  checkTermBoundary int
    (Term "seg" $ tele2Subst (Tele [Formula [Disj [Conj 1, Conj 2]]]) 2)
    (Boundary [(Term "zero" (constSubst 1), Term "seg" idSubst),(Term "zero" (constSubst 1), Term "seg" idSubst) ])

  checkTermBoundary triangle
    (Term "phi" (Map.fromList [
              (Vert [e0, e0] , Vert [e0, e0])
            , (Vert [e0, e1] , Vert [e1, e1])
            , (Vert [e1, e0] , Vert [e0, e1])
            , (Vert [e1, e1] , Vert [e1, e1])
              ]))
    (Boundary [(Term "phi" (Map.fromList [
              (Vert [e0] , Vert [e0, e0])
            , (Vert [e1] , Vert [e1, e1])
              ]), Term "g" idSubst),(Term "f" idSubst, Term "z" (constSubst 1)) ])

  checkFindContortion loopspace
    (Boundary [ (Term "p" andOrSubst , Term "a" (constSubst 2)) , (Term "a" (constSubst 2) , Term "a" (constSubst 2)) , (Term "a" (constSubst 2) , Term "a" (constSubst 2)) ])
    (Term "p" (Map.fromList [
              (Vert [e0, e0, e0] , Vert [e0, e0])
            , (Vert [e0, e0, e1] , Vert [e0, e1])
            , (Vert [e0, e1, e0] , Vert [e0, e1])
            , (Vert [e0, e1, e1] , Vert [e1, e1])
            , (Vert [e1, e0, e0] , Vert [e0, e1])
            , (Vert [e1, e0, e1] , Vert [e0, e1])
            , (Vert [e1, e1, e0] , Vert [e0, e1])
            , (Vert [e1, e1, e1] , Vert [e1, e1])
              ]))

  checkSolve int
    (Boundary [(Term "one" (constSubst 0) , Term "zero" (constSubst 0))])
    (Comp (Box [(Term "seg" idSubst , Term "zero" (constSubst 1))] (Term "zero" (constSubst 1))))

  checkSolve twopaths
    (Boundary [(Term "f" idSubst, Term "g" idSubst) , (Term "f" idSubst, Term "g" idSubst)])
    (Comp (Box [(Term "f" app1Subst , Term "g" andSubst) , (Term "f" app1Subst , Term "g" andSubst)] (Term "f" orSubst)))

  checkSolve triangle
    (Boundary [(Term "h" idSubst, Term "g" idSubst) , (Term "f" idSubst, Term "z" (constSubst 1))])
    (Comp (Box [(Term "h" andSubst , Term "g" app1Subst) , (Term "f" app1Subst , Term "h" orSubst)] (Term "phi" (tele2Subst swap 2))))

  checkSolve gp
    (Boundary [ (Comp (inv "o" "o" "b") , Comp (inv "o" "o" "b")) , (Term "a" idSubst , Term "a" idSubst) ])
    (Comp (Box [(Filler (inv "o" "o" "b") , Filler (inv "o" "o" "b")) , (Term "law" (tele2Subst swap 2) , Term "a" app1Subst )] (Term "a" app1Subst)))

  checkSolve int
    (Boundary [(Term "zero" (constSubst 1) , Term "one" (constSubst 1)) , (Comp (comp "zero" (Term "seg" idSubst) (Term "one" (constSubst 1))) , Term "seg" idSubst)])
    (Comp (Box [ (Term "zero" (constSubst 2), Term "one" (constSubst 2)),
                 ((Filler (Box [(Term "zero" (constSubst 1),
                                Term "one" (constSubst 1))]
                           (Term "seg" idSubst))),
                   Term "seg" app1Subst)] (Term "seg" app1Subst)))


-- intApp1Term = Term "seg" $ tele2Subst (Tele [Formula [Disj [Conj 1]]]) 2
-- intApp1Boundary = Boundary [(Term "zero" (constSubst 2) , Term "one" (constSubst 2)) , (idT "seg" 1 , idT "seg" 1)]

-- intAnd2Term = Term "seg" $ tele2Subst (Tele [Formula [Disj [Conj 2]]]) 2
-- intApp2Boundary = Boundary [(Term "seg" app1Subst , Term "seg" app1Subst) , (Term "zero" (constSubst 2) , Term "one" (constSubst 2))]

-- intAndTerm = Term "seg" $ tele2Subst (Tele [Formula [Disj [Conj 1, Conj 2]]]) 2
-- intAndBoundary = Boundary [(Term "zero" (constSubst 2) , idT "seg" 1) , (Term "zero" (constSubst 2) , idT "seg" 1)]

-- intOrTerm = Term "seg" $ tele2Subst (Tele [Formula [Disj [Conj 1], Disj [Conj 2]]]) 2
-- intOrBoundary = Boundary [(Term "seg" app1Subst , Term "one" (constSubst 2)) , (Term "seg" app1Subst , Term "one" (constSubst 2))]
