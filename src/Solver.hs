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
import Subst

-- Check fibrancy of extension types: cofibration only mentions interval variables which are bound in the extension type https://discord.com/channels/954089080197611551/1007614554647306240/1010200102469632010
-- TODO IMPLEMENT!


type CVar = Int

type Solving s a = StateT (SEnv s) (ExceptT String IO) a

data SEnv s =
  SEnv { cube :: Cube
       , goal :: Type
       , varSupply :: Int
       , varMap :: CVarMap s
       , verbose :: Bool
       }

mkSEnv c g = SEnv c g 0 Map.empty True

data CVarInfo a = CVarInfo { delayedConstraints :: Solving a (), values :: [PTerm] }
type CVarMap a = Map Int (CVarInfo a)

trace :: String -> Solving s ()
trace s = do
  b <- gets verbose
  when b $ liftIO (putStrLn s)

lookupDef :: Id -> Solving s Type
lookupDef name = do
  cube <- gets cube
  case lookup name (map decl2pair (constr cube)) of
    Just face -> return face
    Nothing -> throwError $ "Could not find definition of " ++ name

dimTerm :: Id -> Solving s Int
dimTerm id = do
  ty <- lookupDef id
  return $ dim ty


vertices :: Solving s [Term]
vertices = do
  cube <- gets cube
  return [ emptT id | Decl id ty <- constr cube , dim ty == 0 ]




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



evalType :: Type -> Vert -> Solving s Point
-- evalType f (Vert []) = return $ Point f -- What goes here?
evalType (Type [(Term a _ , Term b _)]) (Vert [Endpoint e]) = return $ Point (if e then b else a)
evalType (Type [(Term a _ , Term b _) , _]) (Vert [Endpoint e , Endpoint e']) =
  evalPoint (if e then b else a) (Vert [Endpoint e'])


evalPoint :: Id -> Vert -> Solving s Point
evalPoint f (Vert []) = return $ Point f
evalPoint f (Vert [Endpoint e]) = do
  Type [(Term a _ , Term b _)] <- lookupDef f
  return $ Point (if e then b else a)
evalPoint f (Vert [Endpoint e , Endpoint e']) = do
  Type [(Term a _ , Term b _) , _] <- lookupDef f
  evalPoint (if e then b else a) (Vert [Endpoint e'])

evalEdge :: Id -> Vert -> Vert -> Solving s (Maybe Term)
evalEdge f v u = do
  case vdiff v u of
    0 -> evalPoint f v >>= \(Point a) -> return (Just (emptT a))
    1 -> do
      d <- dimTerm f
      case d of
        1 -> return $ Just (idT f 1)
        2 -> do
          let (i , Endpoint e) = getPath v u
          Type [(a , b) , (c , d)] <- lookupDef f
          return $ Just $ if i == 1 then (if e then b else a) else (if e then d else c)
    2 -> return Nothing


-- Vertex constraints
--   restrict sigma!x to [ | y <- sigma ! x , evalPoint f y == a ]
--   propagate down...
checkPTerm :: Vert -> [Point] -> PTerm -> Solving s (Maybe PTerm)
checkPTerm x as (PTerm f sigma) = do
  fdim <- dimTerm f
  case fdim of
    0 -> if (Point f `elem` as) then return $ Just (PTerm f sigma) else return Nothing
    _ -> do
      vs <- filterM (\v -> evalPoint f v >>= \b -> return (b `elem` as)) (sigma ! x)
      if null vs
        then return Nothing
        else do
          let sigma' = Map.insert x vs sigma
          -- TODO DOES PROPAGATION NEEDS TO BE RECURSIVE?
          let propagate = Map.mapWithKey (\y us -> filter (\u ->
                                                            (y `above` x) --> any (u `above`) vs &&
                                                            (y `below` x) --> any (u `below`) vs
                                                          ) us) sigma'
          return $ Just (PTerm f propagate)






-- Return only those partial substitutions such that x is one of as
filterPSubsts :: Vert -> [Point] -> [PTerm] -> Solving s [PTerm]
filterPSubsts x as pts = mapM (checkPTerm x as) pts >>= return . catMaybes

equalVertex :: Vert -> Vert -> CVar -> CVar -> Solving s ()
equalVertex v u = addBinaryConstraint $ \x y -> do
  xs <- lookupDom x
  ys <- lookupDom y

  -- Find all the points that v could be with the partial substitutions in the domain
  pxv <- mapM (\(PTerm f s) -> mapM (evalPoint f) (s ! v)) xs >>= return . nub . concat
  pyu <- mapM (\(PTerm f s) -> mapM (evalPoint f) (s ! u)) ys >>= return . nub . concat
  let ps = intersect pxv pyu

  xs' <- filterPSubsts v ps xs
  ys' <- filterPSubsts u ps ys
  guard $ not $ null xs'
  guard $ not $ null ys'
  when (xs' /= xs) $ update x xs'
  when (ys' /= ys) $ update y ys'

equalVertices :: CVar -> CVar -> [(Vert , Vert)] -> Solving s ()
equalVertices x y vus = mapM (\(v,u) -> equalVertex v u x y) vus >> return ()




-- Edge constraints

getEdges :: PTerm -> IVar -> Endpoint -> Solving s [Term]
getEdges ps i e = do
  -- trace $ show ps ++ " | " ++ show i ++ "@" ++ show e
  let PTerm f sigma = ps
  let vs = sigma ! Vert (map (\j -> if i /= j then e else e0) [1..2])
  let us = sigma ! Vert (map (\j -> if i /= j then e else e1) [1..2])
  -- trace $ show vs ++ " --> " ++ show us

  mapM (\v -> mapM (evalEdge f v) (filter (`below` v) us)) vs >>= return . catMaybes . concat


-- TODO COMPUTE BOUNDARY ONLY ONCE BY KEEPING TRACK OF WHICH ASSIGNMENTS GAVE RISE TO CERTAIN BOUNDARY
checkPTermEdge :: IVar -> Endpoint -> [Term] -> PTerm -> Solving s (Maybe PTerm)
checkPTermEdge i e fs (PTerm f sigma) = do
  fdim <- dimTerm f
  case fdim of
    0 -> if (emptT f `elem` fs) then return $ Just (PTerm f sigma) else return Nothing
    _ -> do
      -- trace $ show "Restrict " ++ show (f , sigma) ++ "|" ++ show i ++ "@" ++ show e ++ " to boundaries " ++ show fs

      let x = Vert (map (\j -> if i /= j then e else e0) [1..2])
      let y = Vert (map (\j -> if i /= j then e else e1) [1..2])

      let vs = sigma ! x
      let us = sigma ! y

      vs' <- filterM (\v -> anyM (\u -> evalEdge f v u >>= \g ->
                                     case g of
                                       Just g' -> return (g' `elem` fs)
                                       Nothing -> return False
                                     ) us) vs
      us' <- filterM (\u -> anyM (\v -> evalEdge f v u >>= \g ->
                                     case g of
                                       Just g' -> return (g' `elem` fs)
                                       Nothing -> return False
                                     ) vs') us
      if null vs' || null us'
        then return Nothing
        else do
          let sigma' = Map.insert x vs' sigma
          let sigma'' = Map.insert x vs' sigma'
          let propagate = Map.mapWithKey (\z ws -> filter (\w ->
                                                            (z `above` x) --> any (w `above`) vs' &&
                                                            (z `below` x) --> any (w `below`) vs' &&
                                                            (z `above` y) --> any (w `above`) us' &&
                                                            (z `below` y) --> any (w `below`) us'
                                                          ) ws) sigma''
          return $ Just (PTerm f propagate)


filterPSubstsEdge :: IVar -> Endpoint -> [Term] -> [PTerm] -> Solving s [PTerm]
filterPSubstsEdge i e fs ss = mapM (checkPTermEdge i e fs) ss >>= return . catMaybes

equalEdge :: IVar -> Endpoint -> IVar -> Endpoint -> CVar -> CVar -> Solving s ()
equalEdge i e j e' = addBinaryConstraint $ \x y -> do
  xs <- lookupDom x
  ys <- lookupDom y

  exs <- mapM (\sigma -> getEdges sigma i e) xs >>= return . nub . concat
  eys <- mapM (\sigma -> getEdges sigma j e') ys >>= return . nub . concat

  -- TODO rename to fs to avoid clash with endpoint lists es
  let es = intersect exs eys

  xs' <- filterPSubstsEdge i e es xs
  ys' <- filterPSubstsEdge j e' es ys
  guard $ not $ null xs'
  guard $ not $ null ys'
  when (xs' /= xs) $ update x xs'
  when (ys' /= ys) $ update y ys'


firstSubst :: CVar -> Solving s PTerm
firstSubst var = do
  vals <- lookupDom var
  let PTerm id sigma = head vals
  let newval = PTerm id (injPSubst (fstSubst sigma))
  when ([newval] /= vals) $ update var [newval]
  return newval

-- What to do with degeneracies equivalent to a face? e.g.
-- "seg" fromList [(0,[0]),(1,[0])]
-- is the same as its left face
comp :: Type -> Solving s [Term]
comp (Type [(Term a (Tele []) , Term b (Tele []))]) = do
  let gdim = 1
  Cube cube <- gets cube

  let pterms = map (\f -> createPTerm f gdim) cube

  side0 <- filterPSubsts (Vert [e1]) [Point a] pterms >>= newCVar
  side1 <- filterPSubsts (Vert [e1]) [Point b] pterms >>= newCVar
  back <- newCVar pterms

  lookupDom side0 >>= trace . show
  lookupDom side1 >>= trace . show
  lookupDom back >>= trace . show

  equalVertices side0 back [(Vert [e0] , Vert [e0])]
  equalVertices side1 back [(Vert [e0] , Vert [e1])]

  lookupDom side0 >>= trace . show
  lookupDom side1 >>= trace . show
  lookupDom back >>= trace . show

  res <- mapM (\s -> firstSubst s >>= \(PTerm f sigma) -> return $ Term f ((subst2Tele . fstSubst) sigma))
    (side0 : side1 : back : [])

  lookupDom side0 >>= trace . show
  lookupDom side1 >>= trace . show
  lookupDom back >>= trace . show

  return [Comp (Box [((res !! 0) , res !! 1)] (res !! 2))]


comp (Type [(Term k r, Term l s), (m,n)]) = do
  let gdim = 2
  Cube cube <- gets cube

  -- Initialize the variables and domains
  let pterms = map (\f -> createPTerm f gdim) cube

  v00 <- evalPoint k (Vert [e0])
  v01 <- evalPoint k (Vert [e1])
  v10 <- evalPoint l (Vert [e0])
  v11 <- evalPoint l (Vert [e1])

  sidei0 <- filterPSubsts (Vert [e1,e0]) [v00] pterms >>= filterPSubsts (Vert [e1,e1]) [v01] >>= filterPSubstsEdge 2 e1 [Term k r] >>= newCVar
  sidei1 <- filterPSubsts (Vert [e1,e0]) [v10] pterms >>= filterPSubsts (Vert [e1,e1]) [v11] >>= filterPSubstsEdge 2 e1 [Term l s] >>= newCVar
  sidej0 <- filterPSubsts (Vert [e1,e0]) [v00] pterms >>= filterPSubsts (Vert [e1,e1]) [v10] >>= filterPSubstsEdge 2 e1 [m] >>= newCVar
  sidej1 <- filterPSubsts (Vert [e1,e0]) [v01] pterms >>= filterPSubsts (Vert [e1,e1]) [v11] >>= filterPSubstsEdge 2 e1 [n] >>= newCVar
  back <- newCVar pterms

  trace $ "INITIAL DOMAINS"
  lookupDom sidei0 >>= trace . show
  lookupDom sidei1 >>= trace . show
  lookupDom sidej0 >>= trace . show
  lookupDom sidej1 >>= trace . show
  lookupDom back >>= trace . show


  -- Ensure that all vertices coincide

  equalVertices sidei0 back [(Vert [e0, e0] , Vert [e0 , e0]) , (Vert [e0,e1] , Vert [e0,e1])]
  equalVertices sidei1 back [(Vert [e0, e0] , Vert [e1 , e0]) , (Vert [e0,e1] , Vert [e1,e1])]
  equalVertices sidej0 back [(Vert [e0, e0] , Vert [e0 , e0]) , (Vert [e0,e1] , Vert [e1,e0])]
  equalVertices sidej1 back [(Vert [e0, e0] , Vert [e0 , e1]) , (Vert [e0,e1] , Vert [e1,e1])]

  equalVertices sidei0 sidej0 [(Vert [e0, e0] , Vert [e0 , e0]) , (Vert [e1,e0] , Vert [e1,e0])]
  equalVertices sidei1 sidej0 [(Vert [e0, e0] , Vert [e0 , e1]) , (Vert [e1,e0] , Vert [e1,e1])]
  equalVertices sidei0 sidej1 [(Vert [e0, e1] , Vert [e0 , e0]) , (Vert [e1,e1] , Vert [e1,e0])]
  equalVertices sidei1 sidej1 [(Vert [e0, e1] , Vert [e0 , e1]) , (Vert [e1,e1] , Vert [e1,e1])]

  trace "AFTER VERTEX MATCH"
  lookupDom sidei0 >>= trace . show
  lookupDom sidei1 >>= trace . show
  lookupDom sidej0 >>= trace . show
  lookupDom sidej1 >>= trace . show
  lookupDom back >>= trace . show


  -- Ensure that the edges match
  equalEdge 1 e0 1 e0 sidei0 sidej0
  equalEdge 1 e1 1 e0 sidei0 sidej1
  equalEdge 1 e0 1 e1 sidei1 sidej0
  equalEdge 1 e1 1 e1 sidei1 sidej1

  equalEdge 2 e0 2 e0 sidei0 back
  equalEdge 2 e0 2 e1 sidei1 back
  equalEdge 2 e0 1 e0 sidej0 back
  equalEdge 2 e0 1 e1 sidej1 back

  trace "AFTER EDGES MATCH"
  lookupDom sidei0 >>= trace . show
  lookupDom sidei1 >>= trace . show
  lookupDom sidej0 >>= trace . show
  lookupDom sidej1 >>= trace . show
  lookupDom back >>= trace . show

  -- mapM firstSubst (sidei0 : sidei1 : sidej0 : sidej1 : back : [])

  res <- mapM (\s -> firstSubst s >>= \(PTerm f sigma) -> return $ Term f ((subst2Tele . fstSubst) sigma))
    (sidei0 : sidei1 : sidej0 : sidej1 : back : [])

  trace "FIRST SOLUTION"
  lookupDom sidei0 >>= trace . show
  lookupDom sidei1 >>= trace . show
  lookupDom sidej0 >>= trace . show
  lookupDom sidej1 >>= trace . show
  lookupDom back >>= trace . show

  return [Comp (Box [((res !! 0) , res !! 1) , ((res !! 2) , res !! 3)] (res !! 4))]



comp (Type [(Term k _, Comp (Box [(Term f _ , Term g _)] b)), (m,n)]) = do
  let gdim = 2
  Cube cube <- gets cube
  let pterms = map (\f -> createPTerm f gdim) cube

  -- TODO UNFOLD HCOMP

  return []


comp goal = do

  return []




simpleSolve :: Decl -> Solving s [Term]
simpleSolve (Decl id ty) = do
  goal <- gets goal
  trace $ "TRY TO FIT " ++ id

  cvar <- newCVar [(createPTerm (Decl id ty) (dim goal))]

  case dim goal of
    _ -> do
      let points = createPoset (dim goal)
      mapM (\x -> do
              -- addConstraint cvar (
              --   do
                  [sigma] <- lookupDom cvar
                  v <- evalType goal x
                  res <- checkPTerm x [v] sigma
                  trace $ show res
                  case res of
                    Nothing -> guard False
                    Just sigma' -> when (sigma /= sigma') (update cvar [sigma'])
                                      -- )
          ) points
    2 -> do
      let points = createPoset (dim goal)
      let edges = concat $ map (\v -> [ (v , u) | u <- points, v `above` u , vdiff v u == 1 ]) points
      trace $ show edges
      return []

  -- mapM (\x -> do
  --          [sigma] <- lookupDom cvar
  --          v <- evalType goal x
  --          res <- checkPTermEdge x [v] sigma
  --          trace $ show res
  --          case res of
  --            Nothing -> guard False
  --            Just sigma' -> update cvar [sigma']
  --      ) edges

  lookupDom cvar >>= trace . show

  res <- firstSubst cvar >>= \(PTerm id sigma) -> return $ Term id ((subst2Tele . fstSubst) sigma)
  return [res]


solver :: Cube -> Type -> IO ()
solver cube goal = do
  putStrLn "CUBE"
  mapM (putStrLn . show) (constr cube)
  putStrLn "GOAL"
  putStrLn $ show goal

  -- RUN SIMPLE SOLVE FOR ALL FACES
  simp <- mapM (\face -> runExceptT $ runStateT (simpleSolve face) (mkSEnv cube goal)) (constr cube)


  -- RUN KAN COMPOSITION SOLVER
  if not (null (rights simp))
    then do
      putStrLn "FOUND SIMPLE SOLUTIONS"
      (putStrLn . show) (concat (map fst (rights simp)))
    else do
      res <- runExceptT $ runStateT (comp goal) (mkSEnv cube goal)
      return ()

  return ()
