module CompSolver where

import Control.Monad
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
import Formula


compSolve :: Solving s [Term]
compSolve = do
  cube <- gets cube
  goal <- gets goal

  trace "RUNNING COMPOSITION SOLVER"
  let pterms = map (\f -> createPTerm f (dim goal)) (constr cube)

  let is = [0..(dim goal - 1)]

  let subp = createPoset (dim goal -1)
  let faces = getFaces (dim goal) (dim goal - 1)
  trace $ show faces

  sides0 <- mapM (\i -> do
                     trace $ show $ dim goal - i
                     a <- evalBoundary goal (map (insInd (dim goal - 1 - i) e0) subp)
                     ts <- filterPSubsts (map (e1 `insv`) (createPoset (dim goal -1))) [a] pterms
                     newCVar ts) [0..(dim goal - 1)]
  sides1 <- mapM (\i -> do
                     a <- evalBoundary goal (map (insInd (dim goal - 1 - i) e1) subp)
                     ts <- filterPSubsts (map (e1 `insv`) (createPoset (dim goal -1))) [a] pterms
                     newCVar ts) [0..(dim goal - 1)]
  back <- newCVar pterms

  trace "INITIAL DOMAINS"
  mapM_ (lookupDom >=> trace . show) sides0
  mapM_ (lookupDom >=> trace . show) sides1
  mapM_ (lookupDom >=> trace . show) [back]

  -- Impose back constraints
  mapM_ (\i -> boundaryConstraint (map (e0 `insv`) subp) (faces !! i) (sides0 !! i) back) is
  mapM_ (\i -> boundaryConstraint (map (e0 `insv`) subp) (faces !! (i + dim goal)) (sides1 !! i) back) is

  trace "AFTER BACK CONSTRAINTS"
  mapM_ (lookupDom >=> trace . show) sides0
  mapM_ (lookupDom >=> trace . show) sides1
  mapM_ (lookupDom >=> trace . show) [back]

  mapM_ (\i -> mapM_ (\j -> trace $ show i ++ show j) [i + 1 .. dim goal - 1]) is
  mapM_ (\i -> mapM_ (\j -> boundaryConstraint (map (insInd i e0) subp) (map (insInd i e0) subp) (sides0 !! i) (sides0 !! j)) [i + 1 .. dim goal - 1]) is
  mapM_ (\i -> mapM_ (\j -> boundaryConstraint (map (insInd i e1) subp) (map (insInd i e0) subp) (sides0 !! i) (sides1 !! j)) [i + 1 .. dim goal - 1]) is
  mapM_ (\i -> mapM_ (\j -> boundaryConstraint (map (insInd i e0) subp) (map (insInd i e1) subp) (sides1 !! i) (sides0 !! j)) [i + 1 .. dim goal - 1]) is
  mapM_ (\i -> mapM_ (\j -> boundaryConstraint (map (insInd i e1) subp) (map (insInd i e1) subp) (sides1 !! i) (sides1 !! j)) [i + 1 .. dim goal - 1]) is

  trace "AFTER SIDE CONSTRAINTS"
  mapM_ (lookupDom >=> trace . show) sides0
  mapM_ (lookupDom >=> trace . show) sides1
  mapM_ (lookupDom >=> trace . show) [back]

  mapM_ firstSubst (sides0 ++ sides1 ++ [back])

  trace "FIRST SOLUTION"
  res0 <- map (pterm2term . head) <$> mapM lookupDom sides0
  res1 <- map (pterm2term . head) <$> mapM lookupDom sides1
  resb <- pterm2term . head <$> lookupDom back

  -- res0 <- map pterm2term <$> mapM firstSubst sides0
  -- res1 <- map pterm2term <$> mapM firstSubst sides1
  -- resb <- pterm2term <$> firstSubst back

  return [Comp (Box (zip res0 res1) resb)]

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


  
-- -- Return only those partial substitutions such that x is one of as
-- filterPSubsts :: Vert -> [Term] -> [PTerm] -> Solving s [PTerm]
-- filterPSubsts x as pts = catMaybes <$> mapM (checkPTerm x as) pts
--   -- <*> to separate multiple arguments

-- equalVertex :: Vert -> Vert -> CVar -> CVar -> Solving s ()
-- equalVertex v u = addBinaryConstraint $ \x y -> do
--   xs <- lookupDom x
--   ys <- lookupDom y

--   -- Find all the points that v could be with the partial substitutions in the domain
--   pxv <- nub . concat <$> mapM (\(PTerm f s) -> mapM (evalPoint f) (s ! v)) xs
--   pyu <- nub . concat <$> mapM (\(PTerm f s) -> mapM (evalPoint f) (s ! u)) ys
--   let ps = intersect pxv pyu

--   xs' <- filterPSubsts v ps xs
--   ys' <- filterPSubsts u ps ys
--   guard $ not $ null xs'
--   guard $ not $ null ys'
--   when (xs' /= xs) $ update x xs'
--   when (ys' /= ys) $ update y ys'

-- equalVertices :: CVar -> CVar -> [(Vert , Vert)] -> Solving s ()
-- equalVertices x y vus = mapM (\(v,u) -> equalVertex v u x y) vus >> return ()




-- -- Edge constraints

-- getEdges :: PTerm -> IVar -> Endpoint -> Solving s [Term]
-- getEdges ps i e = do
--   -- trace $ show ps ++ " | " ++ show i ++ "@" ++ show e
--   let PTerm f sigma = ps
--   let vs = sigma ! Vert (map (\j -> if i /= j then e else e0) [1..2])
--   let us = sigma ! Vert (map (\j -> if i /= j then e else e1) [1..2])
--   -- trace $ show vs ++ " --> " ++ show us

--   mapM (\v -> mapM (evalEdge f v) (filter (`below` v) us)) vs >>= return . catMaybes . concat


-- -- TODO COMPUTE BOUNDARY ONLY ONCE BY KEEPING TRACK OF WHICH ASSIGNMENTS GAVE RISE TO CERTAIN BOUNDARY
-- checkPTermEdge :: IVar -> Endpoint -> [Term] -> PTerm -> Solving s (Maybe PTerm)
-- checkPTermEdge i e fs (PTerm f sigma) = do
--   fdim <- dimTerm f
--   case fdim of
--     0 -> if (emptT f `elem` fs) then return $ Just (PTerm f sigma) else return Nothing
--     _ -> do
--       -- trace $ show "Restrict " ++ show (f , sigma) ++ "|" ++ show i ++ "@" ++ show e ++ " to boundaries " ++ show fs

--       let x = Vert (map (\j -> if i /= j then e else e0) [1..2])
--       let y = Vert (map (\j -> if i /= j then e else e1) [1..2])

--       let vs = sigma ! x
--       let us = sigma ! y

--       vs' <- filterM (\v -> anyM (\u -> evalEdge f v u >>= \g ->
--                                      case g of
--                                        Just g' -> return (g' `elem` fs)
--                                        Nothing -> return False
--                                      ) us) vs
--       us' <- filterM (\u -> anyM (\v -> evalEdge f v u >>= \g ->
--                                      case g of
--                                        Just g' -> return (g' `elem` fs)
--                                        Nothing -> return False
--                                      ) vs') us
--       if null vs' || null us'
--         then return Nothing
--         else do
--           let sigma' = Map.insert x vs' sigma
--           let sigma'' = Map.insert x vs' sigma'
--           let propagate = Map.mapWithKey (\z ws -> filter (\w ->
--                                                             (z `above` x) --> any (w `above`) vs' &&
--                                                             (z `below` x) --> any (w `below`) vs' &&
--                                                             (z `above` y) --> any (w `above`) us' &&
--                                                             (z `below` y) --> any (w `below`) us'
--                                                           ) ws) sigma''
--           return $ Just (PTerm f propagate)





-- filterPSubstsEdge :: IVar -> Endpoint -> [Term] -> [PTerm] -> Solving s [PTerm]
-- filterPSubstsEdge i e fs ss = mapM (checkPTermEdge i e fs) ss >>= return . catMaybes

-- equalEdge :: IVar -> Endpoint -> IVar -> Endpoint -> CVar -> CVar -> Solving s ()
-- equalEdge i e j e' = addBinaryConstraint $ \x y -> do
--   xs <- lookupDom x
--   ys <- lookupDom y

--   exs <- mapM (\sigma -> getEdges sigma i e) xs >>= return . nub . concat
--   eys <- mapM (\sigma -> getEdges sigma j e') ys >>= return . nub . concat

--   -- TODO rename to fs to avoid clash with endpoint lists es
--   let es = intersect exs eys

--   xs' <- filterPSubstsEdge i e es xs
--   ys' <- filterPSubstsEdge j e' es ys
--   guard $ not $ null xs'
--   guard $ not $ null ys'
--   when (xs' /= xs) $ update x xs'
--   when (ys' /= ys) $ update y ys'



-- What to do with degeneracies equivalent to a face? e.g.
-- "seg" fromList [(0,[0]),(1,[0])]
-- is the same as its left face


-- evalFace :: Term -> Vert -> Solving s Term
-- evalFace (Term f s) x = do
--   goal <- gets goal
--   let sigma = tele2Subst s (dim goal - 1)
--   trace $ show sigma

--   return $ emptT "asd"

-- evalBoundary :: Boundary -> Vert -> Solving s Term
-- evalBoundary (Boundary ((a , b) : _)) (Vert (Endpoint e : es)) =
--   evalFace (if e then b else a) (Vert es)

-- evalBoundary (Boundary [(Term a _ , Term b _)]) (Vert [Endpoint e]) = return $ Point (if e then b else a)
-- evalBoundary (Boundary [(Term a _ , Term b _) , _]) (Vert [Endpoint e , Endpoint e']) =
--   evalPoint (if e then b else a) (Vert [Endpoint e'])
-- evalBoundary (Boundary [(Term a _ , Term b _) , _ , _]) (Vert (Endpoint e : es)) =
--   evalPoint (if e then b else a) (Vert es)


-- evalBoundary1 :: Boundary -> [Vert] -> Solving s Term
-- -- evalBoundary1 (Boundary [(Term a _ , Term b _)]) (Vert [Endpoint e]) (Vert [Endpoint e]) = return $ Point (if e then b else a)
-- evalBoundary1 (Boundary fs) [x , y] = do
--   let (i , Endpoint e) = getBoundary x y
--   trace $ show i ++ "|" ++ show e
--   let res = (if e then snd else fst) (fs !! (i - 1))
--   trace $ show res
--   return res

-- filterPTerm1 :: [Vert] -> [Term] -> PTerm -> Solving s (Maybe PTerm)
-- filterPTerm1 [x , y] fs (PTerm f sigma) = do
--   fdim <- dimTerm f
--   case fdim of
--     0 -> if (emptT f `elem` fs) then return $ Just (PTerm f sigma) else return Nothing
--     _ -> do
--       let vs = sigma ! x
--       let us = sigma ! y

--       vs' <- filterM (\v -> anyM (\u -> evalEdge f v u >>= \g ->
--                                      case g of
--                                        Just g' -> return (g' `elem` fs)
--                                        Nothing -> return False
--                                      ) us) vs
--       us' <- filterM (\u -> anyM (\v -> evalEdge f v u >>= \g ->
--                                      case g of
--                                        Just g' -> return (g' `elem` fs)
--                                        Nothing -> return False
--                                      ) vs') us
--       if null vs' || null us'
--         then return Nothing
--         else do
--           let sigma' = Map.insert x vs' sigma
--           let sigma'' = Map.insert x vs' sigma'
--           let propagate = Map.mapWithKey (\z ws -> filter (\w ->
--                                                             (z `above` x) --> any (w `above`) vs' &&
--                                                             (z `below` x) --> any (w `below`) vs' &&
--                                                             (z `above` y) --> any (w `above`) us' &&
--                                                             (z `below` y) --> any (w `below`) us'
--                                                           ) ws) sigma''
--           return $ Just (PTerm f propagate)
