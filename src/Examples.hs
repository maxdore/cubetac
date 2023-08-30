{-# LANGUAGE FlexibleContexts #-}
module Examples where

import qualified Data.Map as Map
import Data.Map ((!), Map)


import Poset
import Core
import Deg
import Conn
import Cont


-- Common term constructions

tinv :: Rs r w => Ctxt r w -> Term r w -> Term r w
tinv c t =
  Comp (2, I1) (Ty (termDim c t + 1) [
                     (1,I0) +> t
                   , (1,I1) +> deg c (termFace c t (1,I0)) 1
                   , (2,I0) +> deg c (termFace c t (1,I0)) 1 ])

tcomp :: Rs r w => Ctxt r w -> Term r w -> Term r w -> Term r w
tcomp c t t' = -- TODO CHECK IF COMPOSABLE
  Comp (2, I1) (Ty (termDim c t + 1) [
                     (1,I0) +> deg c (termFace c t (1,I0)) 1
                   , (1,I1) +> t'
                   , (2,I0) +> t ])


t3comp :: Rs r w => Ctxt r w -> Term r w -> Term r w -> Term r w -> Term r w
t3comp c t t' t'' = -- TODO CHECK IF COMPOSABLE (note that here, t is inverted already)
  Comp (2, I1) (Ty (termDim c t + 1) [
                     (1,I0) +> t
                   , (1,I1) +> t''
                   , (2,I0) +> t' ])



twop :: Rs r w => Ctxt r w
twop = [
    ("x" , Ty 0 [])
  , ("y" , Ty 0 [])
  , ("z" , Ty 0 [])
  , ("p" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "y"])
  , ("q" , Ty 1 [(1,I0) +> Var "y" , (1,I1) +> Var "z"])
      ]

invGoal = Ty 1 [ (1,I0) +> Var "y"
               , (1,I1) +> Var "x"
                      ]

invFill , pFill , qFill , pqComp , pqFill :: Rs r w => Term r w
invFill = Fill (2 , I1) (Ty 2 [
                        (1,I0) +> Var "p"
                      , (1,I1) +> deg twop (Var "x") 1
                      , (2,I0) +> deg twop (Var "x") 1
                      ])

pFill = Fill (1,I0) (Ty 2 [
                        (1,I1) +> deg twop (Var "y") 1
                      , (2,I0) +> deg twop (Var "y") 1
                      , (2,I1) +> Var "p"
                      ])
qFill = Fill (1,I1) (Ty 2 [
                        (1,I0) +> deg twop (Var "y") 1
                      , (2,I0) +> deg twop (Var "y") 1
                      , (2,I1) +> Var "q"
                      ])

pqComp = Comp (2,I1) (Ty 2 [
                        (1,I0) +> deg twop (Var "x") 1
                      , (1,I1) +> Var "q"
                      , (2,I0) +> Var "p"
                           ])

pqFill = Fill (2,I1) (Ty 2 [
                        (1,I0) +> deg twop (Var "x") 1
                      , (1,I1) +> Var "q"
                      , (2,I0) +> Var "p"
                           ])

orGoal , andGoal , pqpq :: Rs r w => Ty r w
orGoal = Ty 2 [ (1,I0) +> Var "p"
              , (1,I1) +> deg twop (Var "y") 1
              -- , (2,I0) +> Var "p"
              , (2,I1) +> deg twop (Var "y") 1
                        ]

andGoal = Ty 2 [ (1,I0) +> deg twop (Var "x") 1
               , (1,I1) +> Var "p"
               , (2,I0) +> deg twop (Var "x") 1
               -- , (2,I1) +> Var "p"
                          ]

pqpq = Ty 2 [ (1,I0) +> Var "p"
            , (1,I1) +> Var "q"
            , (2,I0) +> Var "p"
            , (2,I1) +> Var "q"
                      ]

prefl , reflp :: Rs r w => Term r w
prefl = Comp (2,I1) (Ty 2 [
                      (1,I0) +> deg twop (Var "x") 1
                    , (1,I1) +> deg twop (Var "y") 1
                    , (2,I0) +> Var "p"
                        ])

reflp = Comp (2,I1) (Ty 2 [
                      (1,I0) +> deg twop (Var "x") 1
                    , (1,I1) +> Var "p"
                    , (2,I0) +> deg twop (Var "x") 1
                        ])

unitl , unitr :: Rs r w => Ty r w
unitr = Ty 2 [ (1,I0) +> prefl
             , (1,I1) +> Var "p"
             , (2,I0) +> deg twop (Var "x") 1
             , (2,I1) +> deg twop (Var "y") 1
             ]


unitl = Ty 2 [ (1,I0) +> reflp
             , (1,I1) +> Var "p"
             , (2,I0) +> deg twop (Var "x") 1
             , (2,I1) +> deg twop (Var "y") 1
             ]

threep :: Ctxt r w
threep = [
    ("w" , Ty 0 [])
  , ("x" , Ty 0 [])
  , ("y" , Ty 0 [])
  , ("z" , Ty 0 [])
  , ("p" , Ty 1 [(1,I0) +> Var "w" , (1,I1) +> Var "x"])
  , ("q" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "y"])
  , ("r" , Ty 1 [(1,I0) +> Var "y" , (1,I1) +> Var "z"])
      ]

assocback, assocright , assoc , assoc2 , assocOr , assocAnd :: Rs r w => Ty r w
assocback = Ty 2 [ (1,I0) +> tcomp threep (Var "p") (Var "q")
                 , (1,I1) +> Var "p"
                 , (2,I0) +> deg threep (Var "w") 1
             ]

assocright = Ty 2 [ (1,I0) +> Var "r"
                  , (1,I1) +> tcomp threep (Var "q") (Var "r")
                  , (2,I0) +> tinv threep (Var "q")
                  , (2,I1) +> deg threep (Var "z") 1
             ]

assoc = Ty 2 [ (1,I0) +> tcomp threep (tcomp threep (Var "p") (Var "q")) (Var "r")
             , (1,I1) +> tcomp threep (Var "p") (tcomp threep (Var "q") (Var "r"))
             , (2,I0) +> deg threep (Var "w") 1
             , (2,I1) +> deg threep (Var "z") 1
             ]

assoc2 = Ty 2 [ (1,I0) +> tcomp threep (Var "p") (tcomp threep (Var "q") (Var "r"))
              , (1,I1) +> tcomp threep (tcomp threep (Var "p") (Var "q")) (Var "r")
              , (2,I0) +> deg threep (Var "w") 1
              , (2,I1) +> deg threep (Var "z") 1
              ]

assocOr = Ty 2 [ (1,I0) +> tcomp threep (Var "p") (tcomp threep (Var "q") (Var "r"))
               , (1,I1) +>  deg threep (Var "z") 1
               , (2,I0) +> tcomp threep (tcomp threep (Var "p") (Var "q")) (Var "r")
               , (2,I1) +> deg threep (Var "z") 1
              ]

assocAnd = Ty 2 [ (1,I0) +>  deg threep (Var "w") 1
                , (1,I1) +> tcomp threep (Var "p") (tcomp threep (Var "q") (Var "r"))
                , (2,I0) +> deg threep (Var "w") 1
                , (2,I1) +> tcomp threep (tcomp threep (Var "p") (Var "q")) (Var "r")
              ]

threep' :: Rs r w => Ctxt r w
threep' = [
    ("x" , Ty 0 [])
  , ("p" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "x"])
  , ("q" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "x"])
  , ("r" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "x"])
      ]

assoc' :: Rs r w => Ty r w
assoc' = Ty 2 [
    (1,I0) +> tcomp threep' (tcomp threep' (Var "p") (Var "q")) (Var "r")
  , (1,I1) +> tcomp threep' (Var "p") (tcomp threep' (Var "q") (Var "r"))
  , (2,I0) +> deg threep' (Var "x") 1
  , (2,I1) +> deg threep' (Var "x") 1
      ]


eqsq :: Rs r w => Ctxt r w
eqsq = [
    ("x" , Ty 0 [])
  , ("p" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "x"])
  , ("q" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "x"])
  , ("alpha" , Ty 2 [ (1,I0) +> Var "p"
                    , (1,I1) +> Var "q"
                    , (2,I0) +> deg eqsq (Var "x") 1
                    , (2,I1) +> deg eqsq (Var "x") 1
                    ])
    ]

eqsqinv = Ty 2 [ (1,I0) +> Var "q"
              , (1,I1) +> Var "p"
              -- , (2,I0) +> deg (Var "x") 1
              -- , (2,I1) +> deg (Var "x") 1
              ]


eqsqfill = Fill (1,I1) (Ty 2 [
                       (1,I0) +> Var "q"
                     , (2,I1) +> Var "p"
              ])


higherpq :: Rs r w => Ctxt r w
higherpq = [
    ("a" , (Ty 0 []))
  , ("p" , (Ty 2 [(1,I0) +> deg higherpq (Var "a") 1 ,
                  (1,I1) +> deg higherpq (Var "a") 1 ,
                  (2,I0) +> deg higherpq (Var "a") 1 ,
                  (2,I1) +> deg higherpq (Var "a") 1 ]))
  , ("q" , (Ty 2 [(1,I0) +> deg higherpq (Var "a") 1 ,
                  (1,I1) +> deg higherpq (Var "a") 1 ,
                  (2,I0) +> deg higherpq (Var "a") 1 ,
                  (2,I1) +> deg higherpq (Var "a") 1 ]))
                 ]


-- pq = Box [(Term "a" (constSubst 2) , Term "q" id2Subst) , (Term "a" (constSubst 2) , Term "a" (constSubst 2)) ] (Term "p" id2Subst)
-- qp = Box [(Term "a" (constSubst 2) , Term "p" id2Subst) , (Term "a" (constSubst 2) , Term "a" (constSubst 2)) ] (Term "q" id2Subst)

eckmannHilton :: Rs r w => Ty r w
eckmannHilton =
  Ty 3 [
    --   (1,I0) +> tcomp higherpq (Var "p") (Var "q")
    -- , (1,I1) +> tcomp higherpq (Var "q") (Var "p")
      (1,I0) +> Comp (2,I1) (Ty 3 [
                     (1,I0) +> deg higherpq (deg higherpq (Var "a") 1) 1
                   , (1,I1) +> Var "p"
                   , (2,I0) +> Var "q"
                   , (3,I0) +> deg higherpq (deg higherpq (Var "a") 1) 1
                   , (3,I1) +> deg higherpq (deg higherpq (Var "a") 1) 1
                   ])
     , (1,I1) +> Comp (2,I1) (Ty 3 [
                     (1,I0) +> deg higherpq (deg higherpq (Var "a") 1) 1
                   , (1,I1) +> Var "q"
                   , (2,I0) +> Var "p"
                   , (3,I0) +> deg higherpq (deg higherpq (Var "a") 1) 1
                   , (3,I1) +> deg higherpq (deg higherpq (Var "a") 1) 1
                   ])
    , (2,I0) +> deg higherpq (deg higherpq (Var "a") 1) 1
    , (2,I1) +> deg higherpq (deg higherpq (Var "a") 1) 1
    , (3,I0) +> deg higherpq (deg higherpq (Var "a") 1) 1
    , (3,I1) +> deg higherpq (deg higherpq (Var "a") 1) 1
    -- , (Term "a" (constSubst 2) , Term "a" (constSubst 2)) , (Term "a" (constSubst 2) , Term "a" (constSubst 2))
    ]

ehSquare :: Rs r w => Ty r w
ehSquare = Ty 3 [
      (1,I0) +> Var "p"
    , (1,I1) +> Var "p"
    , (2,I0) +> Var "q"
    , (2,I1) +> Var "q"
    , (3,I0) +> normalise higherpq (deg higherpq (deg higherpq (Var "a") 1) 2)
    , (3,I1) +> normalise higherpq (deg higherpq (deg higherpq (Var "a") 1) 2)
 ]


  -- NORMALISE (1,I0) +>    App (App (Var "a") (1,[])) (2,[[[2]]])



xdeg :: Term Cont PCont
xdeg = App (Var "x") (Map.fromList [(Vert [I0], Vert []) , (Vert [I1], Vert [])])


andOrSubst = Map.fromList [
              (Vert [I0, I0] , Vert [I0, I0])
            , (Vert [I0, I1] , Vert [I0, I1])
            , (Vert [I1, I0] , Vert [I0, I1])
            , (Vert [I1, I1] , Vert [I1, I1])
              ]
switch = Map.fromList [
              (Vert [I0, I0] , Vert [I0, I0])
            , (Vert [I0, I1] , Vert [I1, I0])
            , (Vert [I1, I0] , Vert [I0, I1])
            , (Vert [I1, I1] , Vert [I1, I1])
              ]
dup2 = Map.fromList [
              (Vert [I0, I0] , Vert [I0, I0])
            , (Vert [I0, I1] , Vert [I1, I1])
            , (Vert [I1, I0] , Vert [I0, I0])
            , (Vert [I1, I1] , Vert [I1, I1])
              ]

switchandOrp , andOrpswitch , andOrpdup :: Term Cont PCont
switchandOrp = App (App (Var "p") andOrSubst) switch
andOrpswitch = App (App (Var "p") switch) andOrSubst
andOrpdup = App (App (Var "p") dup2) andOrSubst

test :: Term Cont PCont
test = deg twop pqComp 1


andOrpswitch' , switchandOrp' , andOrpdup' , idp , andp , idx :: Term ConnFormula PPM
-- andOrp = App (Var "alpha") (3 , [[[1,2],[1,3]] , [[1],[2],[3]]])
switchandOrp' = App (App (Var "p") (2 , [[[1,2]],[[1],[2]]])) (2 , [[[2]],[[1]]])
andOrpswitch' = App (App (Var "p") (2 , [[[2]],[[1]]])) (2 , [[[1,2]],[[1],[2]]])
andOrpdup' = App (App (Var "p") (2 , [[[2]],[[2]]])) (2 , [[[1,2]],[[1],[2]]])
idp = App (Var "p") (2 , [[[1]],[[2]]])
andp = App (Var "p") (1 , [[[1]]])
idx = App (Var "x") (0 , [])
