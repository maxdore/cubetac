{-# LANGUAGE FlexibleContexts #-}

module Solver where

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


-- Constraint variables are just indices
type CVar = Int

-- The Solving monad
type Solving s a = StateT (SEnv s) (ExceptT String IO) a

-- For each constraint variable we save the constraints that still need to be checked as well as the current domain
data CVarInfo a = CVarInfo { delayedConstraints :: Solving a (), values :: [PTerm] }

data SEnv s =
  SEnv { cube :: Cube
       , goal :: Boundary
       , varSupply :: Int
       , varMap :: Map Int (CVarInfo s)
       , verbose :: Bool
       }

mkSEnv c g = SEnv c g 0 Map.empty True


trace :: String -> Solving s ()
trace s = do
  b <- gets verbose
  when b $ liftIO (putStrLn s)

lookupDef :: Id -> Solving s Boundary
lookupDef name = do
  cube <- gets cube
  case lookup name (map decl2pair (constr cube)) of
    Just face -> return face
    Nothing -> throwError $ "Could not find definition of " ++ name

dimTerm :: Id -> Solving s Int
dimTerm id = do
  ty <- lookupDef id
  return $ dim ty

-- vertices :: Solving s [Term]
-- vertices = do
--   cube <- gets cube
--   return [ emptT id | Decl id ty <- constr cube , dim ty == 0 ]




-- DOMAIN AND CONSTRAINT MANAGEMENT

newCVar :: [PTerm] -> Solving s Int
newCVar domain = do
    v <- nextCVar
    v `isOneOf` domain
    return v
    where
        nextCVar = do
            s <- get
            let v = varSupply s
            put $ s { varSupply = (v + 1) }
            return v
        x `isOneOf` domain =
            modify $ \s ->
                let vm = varMap s
                    vi = CVarInfo {
                        delayedConstraints = return (),
                        values = domain}
                in
                s { varMap = Map.insert x vi vm }

emptyConstraints :: Solving s ()
emptyConstraints = do
  s <- get
  put $ s { varMap = Map.map (\vi -> CVarInfo { values = values vi , delayedConstraints = return() }) (varMap s) }


lookupDom :: Int -> Solving s [PTerm]
lookupDom x = do
    s <- get
    return . values $ varMap s ! x

update :: Int -> [PTerm] -> Solving s ()
update x i = do
    s <- get
    let vm = varMap s
    let vi = vm ! x
    put $ s { varMap = Map.insert x (vi { values = i }) vm }
    delayedConstraints vi


addConstraint :: Int -> Solving s () -> Solving s ()
addConstraint x constraint = do
    s <- get
    let vm = varMap s
    let vi = vm ! x
    let cs = delayedConstraints vi
    put $ s { varMap =
        Map.insert x (vi { delayedConstraints = cs >> constraint }) vm }

type BinaryConstraint s = Int -> Int -> Solving s ()
addBinaryConstraint :: BinaryConstraint s -> BinaryConstraint s
addBinaryConstraint f x y = do
    let constraint  = f x y
    constraint
    addConstraint x constraint
    addConstraint y constraint



-- Commit to the first substitution of a given constraint variable
firstSubst :: CVar -> Solving s PTerm
firstSubst var = do
  vals <- lookupDom var
  let PTerm id sigma = head vals
  let newval = PTerm id (injPSubst (fstSubst sigma))
  when ([newval] /= vals) $ update var [newval]
  return newval






-- evalPoint :: Id -> Vert -> Solving s Term
-- evalPoint f (Vert []) = return $ emptT f
-- evalPoint f (Vert [Endpoint e]) = do
--   Boundary [(Term a _ , Term b _)] <- lookupDef f
--   return $ emptT (if e then b else a)
-- evalPoint f (Vert [Endpoint e , Endpoint e']) = do
--   Boundary [(Term a _ , Term b _) , _] <- lookupDef f
--   evalPoint (if e then b else a) (Vert [Endpoint e'])

-- evalEdge :: Id -> Vert -> Vert -> Solving s (Maybe Term)
-- evalEdge f v u = do
--   case vdiff v u of
--     0 -> evalPoint f v >>= \(Term a _) -> return (Just (Term a (constSubst 2)))
--     1 -> do
--       d <- dimTerm f
--       case d of
--         1 -> return $ Just (idT f 1)
--         2 -> do
--           let (i , Endpoint e) = getBoundary v u
--           Boundary [(a , b) , (c , d)] <- lookupDef f
--           return $ Just $ if i == 1 then (if e then b else a) else (if e then d else c)
--     2 -> return Nothing







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







-- PUT IN MAIN

-- solver :: Cube -> Boundary -> IO ()
-- solver cube goal = do
--   putStrLn "CUBE"
--   mapM (putStrLn . show) (constr cube)
--   putStrLn "GOAL"
--   putStrLn $ show goal

--   -- RUN SIMPLE SOLVE FOR ALL FACES
--   simp <- mapM (\face -> runExceptT $ runStateT (simpleSolve face) (mkSEnv cube goal)) (constr cube)

--   -- RUN KAN COMPOSITION SOLVER
--   if not (null (rights simp))
--     then do
--       putStrLn "FOUND SIMPLE SOLUTIONS"
--       (putStrLn . show) (concat (map fst (rights simp)))
--     else do
--       -- res <- runExceptT $ runStateT (comp goal) (mkSEnv cube goal)
--       return ()

--   return ()
