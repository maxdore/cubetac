module CompSolver where

import Control.Monad.Except
import Control.Monad.State
import Data.Maybe
import Data.List
import qualified Data.Map as Map
import Data.Map ((!), Map)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Either

import qualified Debug.Trace as D

import Prel
import Data
import Poset
import Solver




-- comp :: Type -> Solving s [Term]
-- comp (Type [(Term a (Tele []) , Term b (Tele []))]) = do
--   let gdim = 1
--   Cube cube <- gets cube

--   let pterms = map (\f -> createPTerm f gdim) cube

--   side0 <- filterPSubsts (Vert [e1]) [Point a] pterms >>= newCVar
--   side1 <- filterPSubsts (Vert [e1]) [Point b] pterms >>= newCVar
--   back <- newCVar pterms

--   lookupDom side0 >>= trace . show
--   lookupDom side1 >>= trace . show
--   lookupDom back >>= trace . show

--   equalVertices side0 back [(Vert [e0] , Vert [e0])]
--   equalVertices side1 back [(Vert [e0] , Vert [e1])]

--   lookupDom side0 >>= trace . show
--   lookupDom side1 >>= trace . show
--   lookupDom back >>= trace . show

--   res <- mapM (\s -> firstSubst s >>= \(PTerm f sigma) -> return $ Term f ((subst2Tele . fstSubst) sigma))
--     (side0 : side1 : back : [])

--   lookupDom side0 >>= trace . show
--   lookupDom side1 >>= trace . show
--   lookupDom back >>= trace . show

--   return [Comp (Box [((res !! 0) , res !! 1)] (res !! 2))]


-- comp (Type [(Term k r, Term l s), (m,n)]) = do
--   let gdim = 2
--   Cube cube <- gets cube

--   -- Initialize the variables and domains
--   let pterms = map (\f -> createPTerm f gdim) cube

--   v00 <- evalPoint k (Vert [e0])
--   v01 <- evalPoint k (Vert [e1])
--   v10 <- evalPoint l (Vert [e0])
--   v11 <- evalPoint l (Vert [e1])

--   sidei0 <- filterPSubsts (Vert [e1,e0]) [v00] pterms >>= filterPSubsts (Vert [e1,e1]) [v01] >>= filterPSubstsEdge 2 e1 [Term k r] >>= newCVar
--   sidei1 <- filterPSubsts (Vert [e1,e0]) [v10] pterms >>= filterPSubsts (Vert [e1,e1]) [v11] >>= filterPSubstsEdge 2 e1 [Term l s] >>= newCVar
--   sidej0 <- filterPSubsts (Vert [e1,e0]) [v00] pterms >>= filterPSubsts (Vert [e1,e1]) [v10] >>= filterPSubstsEdge 2 e1 [m] >>= newCVar
--   sidej1 <- filterPSubsts (Vert [e1,e0]) [v01] pterms >>= filterPSubsts (Vert [e1,e1]) [v11] >>= filterPSubstsEdge 2 e1 [n] >>= newCVar
--   back <- newCVar pterms

--   trace $ "INITIAL DOMAINS"
--   lookupDom sidei0 >>= trace . show
--   lookupDom sidei1 >>= trace . show
--   lookupDom sidej0 >>= trace . show
--   lookupDom sidej1 >>= trace . show
--   lookupDom back >>= trace . show


--   -- Ensure that all vertices coincide

--   equalVertices sidei0 back [(Vert [e0, e0] , Vert [e0 , e0]) , (Vert [e0,e1] , Vert [e0,e1])]
--   equalVertices sidei1 back [(Vert [e0, e0] , Vert [e1 , e0]) , (Vert [e0,e1] , Vert [e1,e1])]
--   equalVertices sidej0 back [(Vert [e0, e0] , Vert [e0 , e0]) , (Vert [e0,e1] , Vert [e1,e0])]
--   equalVertices sidej1 back [(Vert [e0, e0] , Vert [e0 , e1]) , (Vert [e0,e1] , Vert [e1,e1])]

--   equalVertices sidei0 sidej0 [(Vert [e0, e0] , Vert [e0 , e0]) , (Vert [e1,e0] , Vert [e1,e0])]
--   equalVertices sidei1 sidej0 [(Vert [e0, e0] , Vert [e0 , e1]) , (Vert [e1,e0] , Vert [e1,e1])]
--   equalVertices sidei0 sidej1 [(Vert [e0, e1] , Vert [e0 , e0]) , (Vert [e1,e1] , Vert [e1,e0])]
--   equalVertices sidei1 sidej1 [(Vert [e0, e1] , Vert [e0 , e1]) , (Vert [e1,e1] , Vert [e1,e1])]

--   trace "AFTER VERTEX MATCH"
--   lookupDom sidei0 >>= trace . show
--   lookupDom sidei1 >>= trace . show
--   lookupDom sidej0 >>= trace . show
--   lookupDom sidej1 >>= trace . show
--   lookupDom back >>= trace . show

--   -- We don't have to check the vertex constraints anymore once we check the edges
--   emptyConstraints

--   -- Ensure that the edges match
--   equalEdge 1 e0 1 e0 sidei0 sidej0
--   equalEdge 1 e1 1 e0 sidei0 sidej1
--   equalEdge 1 e0 1 e1 sidei1 sidej0
--   equalEdge 1 e1 1 e1 sidei1 sidej1

--   equalEdge 2 e0 2 e0 sidei0 back
--   equalEdge 2 e0 2 e1 sidei1 back
--   equalEdge 2 e0 1 e0 sidej0 back
--   equalEdge 2 e0 1 e1 sidej1 back

--   trace "AFTER EDGES MATCH"
--   lookupDom sidei0 >>= trace . show
--   lookupDom sidei1 >>= trace . show
--   lookupDom sidej0 >>= trace . show
--   lookupDom sidej1 >>= trace . show
--   lookupDom back >>= trace . show

--   -- mapM firstSubst (sidei0 : sidei1 : sidej0 : sidej1 : back : [])

--   res <- mapM (\s -> firstSubst s >>= \(PTerm f sigma) -> return $ Term f ((subst2Tele . fstSubst) sigma))
--     (sidei0 : sidei1 : sidej0 : sidej1 : back : [])

--   trace "FIRST SOLUTION"
--   lookupDom sidei0 >>= trace . show
--   lookupDom sidei1 >>= trace . show
--   lookupDom sidej0 >>= trace . show
--   lookupDom sidej1 >>= trace . show
--   lookupDom back >>= trace . show

--   return [Comp (Box [((res !! 0) , res !! 1) , ((res !! 2) , res !! 3)] (res !! 4))]



-- comp (Type [(Term k _, Comp (Box [(Term f _ , Term g _)] b)), (m,n)]) = do
--   let gdim = 2
--   Cube cube <- gets cube
--   let pterms = map (\f -> createPTerm f gdim) cube

--   -- TODO UNFOLD HCOMP
--   return []

-- comp goal = do

--   return []
