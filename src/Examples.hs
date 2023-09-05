{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Examples where

import qualified Data.Map as Map
import Data.Map ((!), Map)


import Poset
import Core
import Rulesets.Cart
import Rulesets.Cont
import Rulesets.Disj
import Rulesets.Dede
import Rulesets.DeMo


-- Common term constructions

tinv :: Rs r w => Ctxt r w -> Term r w -> Term r w
tinv c t =
  Comp (2, I1) (Ty (termDim c t + 1) [
                     (1,I0) +> t
                   , (1,I1) +> App (termFace c t (1,I0)) (deg 0 1)
                   , (2,I0) +> App (termFace c t (1,I0)) (deg 0 1) ])

tcomp :: Rs r w => Ctxt r w -> Term r w -> Term r w -> Term r w
tcomp c t t' = -- TODO CHECK IF COMPOSABLE
  Comp (2, I1) (Ty (termDim c t + 1) [
                     (1,I0) +> App (termFace c t (1,I0)) (deg 0 1)
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
                      , (1,I1) +> App (Var "x") (deg 0 1)
                      , (2,I0) +> App (Var "x") (deg 0 1)
                      ])

pFill = Fill (1,I0) (Ty 2 [
                        (1,I1) +> App (Var "y") (deg 0 1)
                      , (2,I0) +> App (Var "y") (deg 0 1)
                      , (2,I1) +> Var "p"
                      ])
qFill = Fill (1,I1) (Ty 2 [
                        (1,I0) +> App (Var "y") (deg 0 1)
                      , (2,I0) +> App (Var "y") (deg 0 1)
                      , (2,I1) +> Var "q"
                      ])

pqComp = Comp (2,I1) (Ty 2 [
                        (1,I0) +> App (Var "x") (deg 0 1)
                      , (1,I1) +> Var "q"
                      , (2,I0) +> Var "p"
                           ])

pqFill = Fill (2,I1) (Ty 2 [
                        (1,I0) +> App (Var "x") (deg 0 1)
                      , (1,I1) +> Var "q"
                      , (2,I0) +> Var "p"
                           ])

orGoal , andGoal , pqpq :: Rs r w => Ty r w
orGoal = Ty 2 [ (1,I0) +> Var "p"
              , (1,I1) +> App (Var "y") (deg 0 1)
              -- , (2,I0) +> Var "p"
              , (2,I1) +> App (Var "y") (deg 0 1)
                        ]

andGoal = Ty 2 [ (1,I0) +> App (Var "x") (deg 0 1)
               , (1,I1) +> Var "p"
               , (2,I0) +> App (Var "x") (deg 0 1)
               -- , (2,I1) +> Var "p"
                          ]

pqpq = Ty 2 [ (1,I0) +> Var "p"
            , (1,I1) +> Var "q"
            , (2,I0) +> Var "p"
            , (2,I1) +> Var "q"
                      ]

prefl , reflp :: Rs r w => Term r w
prefl = Comp (2,I1) (Ty 2 [
                      (1,I0) +> App (Var "x") (deg 0 1)
                    , (1,I1) +> App (Var "y") (deg 0 1)
                    , (2,I0) +> Var "p"
                        ])

reflp = Comp (2,I1) (Ty 2 [
                      (1,I0) +> App (Var "x") (deg 0 1)
                    , (1,I1) +> Var "p"
                    , (2,I0) +> App (Var "x") (deg 0 1)
                        ])

unitl , unitr :: Rs r w => Ty r w
unitr = Ty 2 [ (1,I0) +> prefl
             , (1,I1) +> Var "p"
             , (2,I0) +> App (Var "x") (deg 0 1)
             , (2,I1) +> App (Var "y") (deg 0 1)
             ]


unitl = Ty 2 [ (1,I0) +> reflp
             , (1,I1) +> Var "p"
             , (2,I0) +> App (Var "x") (deg 0 1)
             , (2,I1) +> App (Var "y") (deg 0 1)
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
                 , (2,I0) +> App (Var "w") (deg 0 1)
             ]

assocright = Ty 2 [ (1,I0) +> Var "r"
                  , (1,I1) +> tcomp threep (Var "q") (Var "r")
                  , (2,I0) +> tinv threep (Var "q")
                  , (2,I1) +> App (Var "z") (deg 0 1)
             ]

assoc = Ty 2 [ (1,I0) +> tcomp threep (tcomp threep (Var "p") (Var "q")) (Var "r")
             , (1,I1) +> tcomp threep (Var "p") (tcomp threep (Var "q") (Var "r"))
             , (2,I0) +> App (Var "w") (deg 0 1)
             , (2,I1) +> App (Var "z") (deg 0 1)
             ]

assoc2 = Ty 2 [ (1,I0) +> tcomp threep (Var "p") (tcomp threep (Var "q") (Var "r"))
              , (1,I1) +> tcomp threep (tcomp threep (Var "p") (Var "q")) (Var "r")
              , (2,I0) +> App (Var "w") (deg 0 1)
              , (2,I1) +> App (Var "z") (deg 0 1)
              ]

assocOr = Ty 2 [ (1,I0) +> tcomp threep (Var "p") (tcomp threep (Var "q") (Var "r"))
               , (1,I1) +>  App (Var "z") (deg 0 1)
               , (2,I0) +> tcomp threep (tcomp threep (Var "p") (Var "q")) (Var "r")
               , (2,I1) +> App (Var "z") (deg 0 1)
              ]

assocAnd = Ty 2 [ (1,I0) +>  App (Var "w") (deg 0 1)
                , (1,I1) +> tcomp threep (Var "p") (tcomp threep (Var "q") (Var "r"))
                , (2,I0) +> App (Var "w") (deg 0 1)
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
  , (2,I0) +> App (Var "x") (deg 0 1)
  , (2,I1) +> App (Var "x") (deg 0 1)
      ]


-- Sphere
sphere :: Rs r w => Ctxt r w
sphere = [
        ("b" , Ty 0 [])
      , ("s" , (Ty 2 [(1,I0) +> ndeg (Var "b") 1 ,
                      (1,I1) +> ndeg (Var "b") 1 ,
                      (2,I0) +> ndeg (Var "b") 1 ,
                      (2,I1) +> ndeg (Var "b") 1 ]))
                 ]

-- andOrSubst = Map.fromList [
--               (Vert [e0, e0] , Vert [e0, e0])
--             , (Vert [e0, e1] , Vert [e0, e1])
--             , (Vert [e1, e0] , Vert [e0, e1])
--             , (Vert [e1, e1] , Vert [e1, e1])
--               ]
andOrSubst = Map.fromList [
              (Vert [I0, I0] , Vert [I0, I0])
            , (Vert [I0, I1] , Vert [I0, I1])
            , (Vert [I1, I0] , Vert [I0, I1])
            , (Vert [I1, I1] , Vert [I1, I1])
              ]


  -- andOrSubst3 = Map.fromList [
  --             (Vert [e0, e0, e0] , Vert [e0, e0])
  --           , (Vert [e0, e0, e1] , Vert [e0, e1])
  --           , (Vert [e0, e1, e0] , Vert [e0, e1])
  --           , (Vert [e0, e1, e1] , Vert [e1, e1])
  --           , (Vert [e1, e0, e0] , Vert [e0, e1])
  --           , (Vert [e1, e0, e1] , Vert [e0, e1])
  --           , (Vert [e1, e1, e0] , Vert [e0, e1])
  --           , (Vert [e1, e1, e1] , Vert [e1, e1])
  --             ]


andOrCont :: Rs Cont w => Ty Cont w
andOrCont = Ty 3 [
    (1,I0) +> App (Var "s") andOrSubst
  , (1,I1) +> ndeg (Var "b") 2
  , (2,I0) +> ndeg (Var "b") 2
  , (2,I1) +> ndeg (Var "b") 2
  , (3,I0) +> ndeg (Var "b") 2
  , (3,I1) +> ndeg (Var "b") 2
      ]

andOrDede :: Rs Dede w => Ty Dede w
andOrDede = Ty 3 [
    (1,I0) +> App (Var "s") (2 , [[[1],[2]],[[1,2]]])
  , (1,I1) +> ndeg (Var "b") 2
  , (2,I0) +> ndeg (Var "b") 2
  , (2,I1) +> ndeg (Var "b") 2
  , (3,I0) +> ndeg (Var "b") 2
  , (3,I1) +> ndeg (Var "b") 2
      ]


-- sphere5Cube = Boundary [ (Term "p" (tele2Subst (Tele [Formula [Disj [Conj 1, Conj 2 , Conj 3 , Conj 4]] , Formula [Disj [Conj 1], Disj [Conj 2] , Disj [Conj 3] , Disj [Conj 4]]]) 4) , Term "a" (constSubst 4)) , (Term "a" (constSubst 4) , Term "a" (constSubst 4)) , (Term "a" (constSubst 4) , Term "a" (constSubst 4)) , (Term "a" (constSubst 4) , Term "a" (constSubst 4)) ,  (Term "a" (constSubst 4) , Term "a" (constSubst 4)) ]





eqsq :: Rs r w => Ctxt r w
eqsq = [
    ("x" , Ty 0 [])
  , ("p" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "x"])
  , ("q" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "x"])
  , ("alpha" , Ty 2 [ (1,I0) +> Var "p"
                    , (1,I1) +> Var "q"
                    , (2,I0) +> App (Var "x") (deg 0 1)
                    , (2,I1) +> App (Var "x") (deg 0 1)
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


sq :: Rs r w => Ctxt r w
sq = [
    ("x" , Ty 0 [])
  , ("p" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "x"])
  , ("q" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "x"])
  , ("r" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "x"])
  , ("s" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "x"])
  , ("alpha" , Ty 2 [ (1,I0) +> Var "p"
                    , (1,I1) +> Var "s"
                    , (2,I0) +> Var "r"
                    , (2,I1) +> Var "q"
                    ])
    ]

symmsq = Ty 2 [ (1,I0) +> Var "r"
              , (1,I1) +> Var "q"
              , (2,I0) +> Var "p"
              , (2,I1) +> Var "s"
                    ]



higherpq :: Rs r w => Ctxt r w
higherpq = [
    ("a" , (Ty 0 []))
  , ("p" , (Ty 2 [(1,I0) +> App (Var "a") (deg 0 1) ,
                  (1,I1) +> App (Var "a") (deg 0 1) ,
                  (2,I0) +> App (Var "a") (deg 0 1) ,
                  (2,I1) +> App (Var "a") (deg 0 1) ]))
  , ("q" , (Ty 2 [(1,I0) +> App (Var "a") (deg 0 1) ,
                  (1,I1) +> App (Var "a") (deg 0 1) ,
                  (2,I0) +> App (Var "a") (deg 0 1) ,
                  (2,I1) +> App (Var "a") (deg 0 1) ]))
                 ]


-- pq = Box [(Term "a" (constSubst 2) , Term "q" id2Subst) , (Term "a" (constSubst 2) , Term "a" (constSubst 2)) ] (Term "p" id2Subst)
-- qp = Box [(Term "a" (constSubst 2) , Term "p" id2Subst) , (Term "a" (constSubst 2) , Term "a" (constSubst 2)) ] (Term "q" id2Subst)

eckmannHilton :: Rs r w => Ty r w
eckmannHilton =
  Ty 3 [
    --   (1,I0) +> tcomp higherpq (Var "p") (Var "q")
    -- , (1,I1) +> tcomp higherpq (Var "q") (Var "p")
      (1,I0) +> Comp (2,I1) (Ty 3 [
                     (1,I0) +> App (App (Var "a") (deg 0 1)) (deg 1 2)
                   , (1,I1) +> Var "p"
                   , (2,I0) +> Var "q"
                   , (3,I0) +> App (App (Var "a") (deg 0 1)) (deg 1 2)
                   , (3,I1) +> App (App (Var "a") (deg 0 1)) (deg 1 2)
                   ])
     , (1,I1) +> Comp (2,I1) (Ty 3 [
                     (1,I0) +> App (App (Var "a") (deg 0 1)) (deg 1 2)
                   , (1,I1) +> Var "q"
                   , (2,I0) +> Var "p"
                   , (3,I0) +> App (App (Var "a") (deg 0 1)) (deg 1 2)
                   , (3,I1) +> App (App (Var "a") (deg 0 1)) (deg 1 2)
                   ])
    , (2,I0) +> App (App (Var "a") (deg 0 1)) (deg 1 2)
    , (2,I1) +> App (App (Var "a") (deg 0 1)) (deg 1 2)
    , (3,I0) +> App (App (Var "a") (deg 0 1)) (deg 1 2)
    , (3,I1) +> App (App (Var "a") (deg 0 1)) (deg 1 2)
    ]

ehSquare :: Rs r w => Ty r w
ehSquare = Ty 3 [
      (1,I0) +> Var "p"
    , (1,I1) +> Var "p"
    , (2,I0) +> Var "q"
    , (2,I1) +> Var "q"
    , (3,I0) +> normalise higherpq (App (App (Var "a") (deg 0 1)) (deg 1 2))
    , (3,I1) +> normalise higherpq (App (App (Var "a") (deg 0 1)) (deg 1 2))
 ]


  -- NORMALISE (1,I0) +>    App (App (Var "a") (1,[])) (2,[[[2]]])



xdeg :: Term Cont PCont
xdeg = App (Var "x") (Map.fromList [(Vert [I0], Vert []) , (Vert [I1], Vert [])])


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

-- test :: Term Cont PCont
-- test = App pqComp 1


andOrpswitch' , switchandOrp' , andOrpdup' , idp , andp , idx :: Term Dede PSubst
-- andOrp = App (Var "alpha") (3 , [[[1,2],[1,3]] , [[1],[2],[3]]])
switchandOrp' = App (App (Var "p") (2 , [[[1,2]],[[1],[2]]])) (2 , [[[2]],[[1]]])
andOrpswitch' = App (App (Var "p") (2 , [[[2]],[[1]]])) (2 , [[[1,2]],[[1],[2]]])
andOrpdup' = App (App (Var "p") (2 , [[[2]],[[2]]])) (2 , [[[1,2]],[[1],[2]]])
idp = App (Var "p") (2 , [[[1]],[[2]]])
andp = App (Var "p") (1 , [[[1]]])
idx = App (Var "x") (0 , [])
