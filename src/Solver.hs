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

import qualified Debug.Trace as D

import Prel
import Data
import Deg

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
  case lookup name (map decl (constr cube)) of
    Just face -> return face
    Nothing -> throwError $ "Could not find definition of " ++ name

dimTerm :: Id -> Solving s Int
dimTerm id = do
  ty <- lookupDef id
  return $ dim ty


vertices :: Solving s [Term]
vertices = do
  cube <- gets cube
  return [ emptT id | Decl (id , ty) <- constr cube , dim ty == 0 ]




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
    put $ s { varMap = Map.insert x (vi { delayedConstraints = return (), values = i }) vm }
    -- put $ s { varMap = Map.insert x (vi { values = i }) vm }
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









-- Vertex constraints

evalPoint :: Id -> Vert -> Solving s Point
evalPoint f (Vert []) = return $ Point f
evalPoint f (Vert [Endpoint e]) = do
  Type [(Term a _ , Term b _)] <- lookupDef f
  return $ Point (if e then b else a)
evalPoint f (Vert [Endpoint e , Endpoint e']) = do
  Type [(Term a _ , Term b _) , _] <- lookupDef f
  evalPoint (if e then b else a) (Vert [Endpoint e'])

--   restrict sigma!x to [ | y <- sigma ! x , evalPoint f y == a ]
--   propagate down...
checkPTerm :: Vert -> [Point] -> PTerm -> Solving s (Maybe PTerm)
checkPTerm x as (PTerm (f, sigma)) = do
  fdim <- dimTerm f
  case fdim of
    0 -> if (Point f `elem` as) then return $ Just (PTerm (f,sigma)) else return Nothing
    _ -> do
      sigmaAtx <- filterM (\v -> evalPoint f v >>= \b -> return (b `elem` as)) (sigma ! x)
      if null sigmaAtx
        then return Nothing
        else do
          let updateX = Map.insert x sigmaAtx sigma
          -- TODO DOES PROPAGATION NEEDS TO BE RECURSIVE?
          let propagate = Map.mapWithKey (\y us -> filter (\u ->
                                                            (y `above` x) --> any (u `above`) sigmaAtx &&
                                                            (y `below` x) --> any (u `below`) sigmaAtx
                                                          ) us) updateX
          return $ Just (PTerm (f , propagate))






-- Return only those partial substitutions such that x is one of as
filterPSubsts :: Vert -> [Point] -> [PTerm] -> Solving s [PTerm]
filterPSubsts x as pts = mapM (checkPTerm x as) pts >>= return . catMaybes

equalVertex :: Vert -> Vert -> CVar -> CVar -> Solving s ()
equalVertex v u = addBinaryConstraint $ \x y -> do
  xs <- lookupDom x
  ys <- lookupDom y

  -- Find all the points that v could be with the partial substitutions in the domain
  pxv <- mapM (\(PTerm (f , s)) -> mapM (evalPoint f) (s ! v)) xs >>= return . nub . concat
  pyu <- mapM (\(PTerm (f , s)) -> mapM (evalPoint f) (s ! u)) ys >>= return . nub . concat
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

evalEdge :: PTerm -> IVar -> Endpoint -> Solving s [Term]
evalEdge (PTerm (f , sigma)) i e = do
  trace "EVAL EDGE"
  trace $ show (f , sigma) ++ " | " ++ show i ++ "@" ++ show e

  let xs = sigma ! Vert (map (\j -> if i /= j then e else e0) [1..2])
  let ys = sigma ! Vert (map (\j -> if i /= j then e else e1) [1..2])
  trace $ show xs ++ " --> " ++ show ys

  mapM (\x -> mapM (evalFromTo x) (filter (`below` x) ys)) xs >>= return . catMaybes . concat
  -- trace $ show res
  -- return undefined
  where
    evalFromTo :: Vert -> Vert -> Solving s (Maybe Term)
    evalFromTo v u = do
      case vdiff v u of
        0 -> return Nothing -- $ Just undefined -- TODO GIVE constant path
        1 -> do
          d <- dimTerm f
          case d of
            1 -> return $ Just (idT f 1)
            2 -> do
              let (i , e') = getPath v u
              getBoundary i e' >>= return . Just
        2 -> return Nothing

    getBoundary :: IVar -> Endpoint -> Solving s Term
    getBoundary i (Endpoint e) = do
      Type [(a , b) , (c , d)] <- lookupDef f
      return $ if i == 1 then (if e then b else a) else (if e then d else c)


checkPTermEdge :: IVar -> Endpoint -> [Term] -> PTerm -> Solving s (Maybe PTerm)
checkPTermEdge i e fs (PTerm (f, sigma)) = do
  fdim <- dimTerm f
  case fdim of
    0 -> if (emptT f `elem` fs) then return $ Just (PTerm (f,sigma)) else return Nothing
    _ -> do
      trace $ show "Restrict " ++ show (f , sigma) ++ " to boundaries " ++ show fs
      return Nothing
      -- sigmaAtx <- filterM (\v -> evalPoint f v >>= \b -> return (b `elem` as)) (sigma ! x)
      -- if null sigmaAtx
      --   then return Nothing
      --   else do
      --     let updateX = Map.insert x sigmaAtx sigma
      --     -- TODO DOES PROPAGATION NEEDS TO BE RECURSIVE?
      --     let propagate = Map.mapWithKey (\y us -> filter (\u ->
      --                                                       (y `above` x) --> any (u `above`) sigmaAtx &&
      --                                                       (y `below` x) --> any (u `below`) sigmaAtx
      --                                                     ) us) updateX
      --     return $ Just (PTerm (f , propagate))


filterPSubstsEdge :: IVar -> Endpoint -> [Term] -> [PTerm] -> Solving s [PTerm]
filterPSubstsEdge i e fs ss = mapM (checkPTermEdge i e fs) ss >>= return . catMaybes

equalEdge :: IVar -> Endpoint -> IVar -> Endpoint -> CVar -> CVar -> Solving s ()
equalEdge i e j e' = addBinaryConstraint $ \x y -> do
  trace "MATCH BOUNDARIES"
  xs <- lookupDom x
  ys <- lookupDom y
  trace $ show xs
  trace $ show ys

  exs <- mapM (\sigma -> evalEdge sigma i e) xs >>= return . nub . concat
  eys <- mapM (\sigma -> evalEdge sigma j e') ys >>= return . nub . concat

  -- TODO rename to fs to avoid clash with endpoint lists es
  let es = intersect exs eys
  trace $ show es

  xs' <- filterPSubstsEdge i e es xs
  ys' <- filterPSubstsEdge j e' es ys
  guard $ not $ null xs'
  guard $ not $ null ys'
  when (xs' /= xs) $ update x xs'
  when (ys' /= ys) $ update y ys'


firstSubst :: CVar -> Solving s PTerm
firstSubst var = do
  vals <- lookupDom var
  let PTerm (id , sigma) = head vals
  let newval = PTerm (id , fstPSubst sigma)
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

  res <- mapM (\s -> firstSubst s >>= \(PTerm (f , sigma)) -> return $ Term f ((subst2Tele . psubst2subst . fstPSubst) sigma))
    (side0 : side1 : back : [])

  lookupDom side0 >>= trace . show
  lookupDom side1 >>= trace . show
  lookupDom back >>= trace . show

  return [Comp (Box [((res !! 0) , res !! 1)] (res !! 2))]


comp (Type [(Term k _, Term l _), (m,n)]) = do
  let gdim = 2
  Cube cube <- gets cube

  -- Initialize the variables and domains
  let pterms = map (\f -> createPTerm f gdim) cube

  v00 <- evalPoint k (Vert [e0])
  v01 <- evalPoint k (Vert [e1])
  v10 <- evalPoint l (Vert [e0])
  v11 <- evalPoint l (Vert [e1])

  -- TODO also filter according to boundaries? Or put this later?
  sidei0 <- filterPSubsts (Vert [e1,e0]) [v00] pterms >>= filterPSubsts (Vert [e1,e1]) [v01] >>= newCVar
  sidei1 <- filterPSubsts (Vert [e1,e0]) [v10] pterms >>= filterPSubsts (Vert [e1,e1]) [v11] >>= newCVar
  sidej0 <- filterPSubsts (Vert [e1,e0]) [v00] pterms >>= filterPSubsts (Vert [e1,e1]) [v10] >>= newCVar
  sidej1 <- filterPSubsts (Vert [e1,e0]) [v01] pterms >>= filterPSubsts (Vert [e1,e1]) [v11] >>= newCVar
  back <- newCVar pterms

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
  equalEdge 1 e1 1 e0 sidei0 sidej1



  trace "AFTER EDGES MATCH"
  lookupDom sidei0 >>= trace . show
  lookupDom sidei1 >>= trace . show
  lookupDom sidej0 >>= trace . show
  lookupDom sidej1 >>= trace . show
  lookupDom back >>= trace . show


  -- Pick out the first solution
  mapM firstSubst (sidei0 : sidei1 : sidej0 : sidej1 : back : [])

  trace "FIRST SOLUTION"
  lookupDom sidei0 >>= trace . show
  lookupDom sidei1 >>= trace . show
  lookupDom sidej0 >>= trace . show
  lookupDom sidej1 >>= trace . show
  lookupDom back >>= trace . show

  return []



comp (Type [(Term k _, Comp (Box [(Term f _ , Term g _)] b)), (m,n)]) = do
  let gdim = 2
  Cube cube <- gets cube
  let pterms = map (\f -> createPTerm f gdim) cube

  -- TODO UNFOLD HCOMP

  return []


comp goal = do

  return []




solve :: Solving s [Term]
solve = do
  trace "CUBE"
  Cube cube <- gets cube
  mapM (\(Decl (face , ty)) -> trace $ face ++ " : " ++ show ty) cube

  trace "GOAL"
  goal <- gets goal
  trace $ show goal

  -- TODO check for direct matches before composing

  comp goal

