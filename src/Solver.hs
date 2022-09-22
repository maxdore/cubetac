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

import Prel
import Data
import Deg

-- Check fibrancy of extension types: cofibration only mentions interval variables which are bound in the extension type https://discord.com/channels/954089080197611551/1007614554647306240/1010200102469632010
-- TODO IMPLEMENT!


type Solving s a = StateT (SEnv s) (ExceptT String IO) a

data SEnv s =
  SEnv { cube :: Cube
       , goal :: Type
       , varSupply :: Int
       , varMap :: VarMap s
       , verbose :: Bool
       }

mkSEnv c g = SEnv c g 0 Map.empty True

data VarInfo a = VarInfo { delayedConstraints :: Solving a (), values :: [PTerm] }
type VarMap a = Map Int (VarInfo a)

trace :: String -> Solving s ()
trace s = do
  b <- gets verbose
  when b $ liftIO (putStrLn s)


lookupDef :: Id -> Solving s Type
lookupDef name = do
  cube <- gets cube
  case lookup name (map decl (faces cube)) of
    Just face -> return face
    Nothing -> throwError $ "Could not find definition of " ++ name

dimTerm :: Id -> Solving s Int
dimTerm id = do
  ty <- lookupDef id
  return $ dim ty


-- deg :: Type -> Solving s [Result]
-- deg goal = do
--   let dims = [1..(dim goal)]

vertices :: Solving s [Term]
vertices = do
  cube <- gets cube
  -- return $ map (\(id , ty) -> emptT id) $ filter (\(id , ty) -> dim ty == 0) cube
  return [ emptT id | Decl (id , ty) <- faces cube , dim ty == 0 ]




-- DOMAIN AND CONSTRAINT MANAGEMENT

newVar :: [PTerm] -> Solving s Int
newVar domain = do
    v <- nextVar
    v `isOneOf` domain
    return v
    where
        -- nextVar :: Solving
        nextVar = do
            s <- get
            let v = varSupply s
            put $ s { varSupply = (v + 1) }
            return v
        -- isOneOf :: Solving -> [Term] -> Solving
        x `isOneOf` domain =
            modify $ \s ->
                let vm = varMap s
                    vi = VarInfo {
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



-- Poset constraint
-- Make sure the map is a poset map!


getBoundary :: Subst -> Int -> Endpoint -> Solving s Term
getBoundary s i e = do
  ty <- lookupDef undefined
  case domdim s of
    -- 1 -> undefined
    2 -> undefined
  return undefined


shareBoundary :: Subst -> Int -> Endpoint -> PTerm -> Int -> Endpoint -> Solving s Bool
shareBoundary sigma i e tau j e' = do

  return False

boundariesAgree :: Int -> Endpoint -> Int -> Endpoint -> Var -> Var -> Solving s ()
boundariesAgree i e j e' = addBinaryConstraint $ \x y -> do
  xv <- lookupDom x
  yv <- lookupDom y

  -- xv' <- filterM (\x' -> anyM (\y' -> boundariesAgree x' i e y' j e') (Set.toList yv)) (Set.toList xv)

  return ()
--     guard $ not $ Set.null (Set.fromList xv')
--     guard $ not $ Set.null (Set.fromList yv')
--     when (xv' /= Set.toList xv) $ update x (Set.fromList xv')
--     when (yv' /= Set.toList yv) $ update y (Set.fromList yv')

verticesAgree :: [(Vert, Vert)] -> Var -> Var -> Solving s ()
verticesAgree vus = addBinaryConstraint $ \x y -> do
  xv <- lookupDom x
  yv <- lookupDom y

  -- xv' <- filterM (\x' -> anyM (\y' -> have x' i e y' j e') (Set.toList yv)) (Set.toList xv)

  return ()

hasValue :: Var -> PTerm -> Solving s ()
var `hasValue` val = do
    vals <- lookupDom var
    guard $ val `elem` vals
    let i = [val]
    -- let i = Set.singleton val
    when (i /= vals) $ update var i


type PSubst = Map Vert [Vert]
newtype PTerm = PTerm { pterm :: (Id , PSubst)}
  deriving (Eq)

instance Show PTerm where
  show (PTerm (id , part)) = show id ++ " " ++ show part



-- in list, later vertices are not necessarily below
-- but all below are later!

createPSubsts :: Int -> Int -> [(Vert , [Vert])]
createPSubsts k l = map (\v -> (v , createGrid l)) (createGrid k)

filterRec :: Vert -> Vert -> [(Vert , [Vert])] -> [(Vert , [Vert])]
filterRec x v ys = map (\(y, us) -> (y , [ u | u <- us , (y `below` x) --> (u `below` v) ])) ys

getSubsts :: [(Vert , [Vert])] -> [[(Vert , Vert)]]
getSubsts [] = [[]]
getSubsts ((x , vs) : ys) = [ (x , v) : r | v <- vs , r <- getSubsts (filterRec x v ys) ]


-- boundaryPTerm :: 


createPTerm :: Decl -> Int -> PTerm
createPTerm (Decl (id , ty)) gdim =
  let parts = map (\v -> (v , createGrid (dim ty))) (createGrid gdim) in
  PTerm (id , Map.fromList parts)


-- getVertex :: Id -> Subst -> Solving s Term
-- getVertex id 


withVerticesAgreeing :: PTerm -> PTerm -> [(Vert,Vert)] -> Solving s (PTerm , PTerm)
withVerticesAgreeing (PTerm (f , sigma)) (PTerm (g , rho)) xys = do
  -- for each ((x,y):xys)
  --   for each u in sigma !! x exists v in rho !! y such that f @ u == g @ v
  let s = Map.toList sigma
  let r = Map.toList rho
  -- map () (zip (s,r))
  return undefined



evalPoint :: Id -> Vert -> Solving s Point
evalPoint f (Vert []) = return $ Point f
evalPoint f (Vert [Endpoint e]) = do
  -- mmh <- lookupDef f
  -- trace $ show f
  -- trace $ show mmh
  Type [(Term (a , _) , Term (b , _))] <- lookupDef f
  return $ Point (if e then b else a)



-- restrictSubst :: Vert -> [Vert] -> PSubst -> PSubst
-- restrictSubst x ys = Map.adjust


checkPTerm :: Vert -> Point -> PTerm -> Solving s (Maybe PTerm)
--   restrict sigma!x to [ | y <- sigma ! x , evalPoint f y == a ]
--   propagate down...
checkPTerm x a (PTerm (f, sigma)) = do
  fdim <- dimTerm f
  case fdim of
    0 -> if (Point f == a) then return $ Just (PTerm (f,sigma)) else return Nothing
    1 -> do
      sigmaAtx <- filterM (\v -> evalPoint f v >>= \b -> return (a == b)) (sigma ! x)
      let updateX = Map.insert x sigmaAtx sigma
      let propagate = Map.mapWithKey (\y us -> filter (\u ->
                                                         (y `above` x) --> any (u `above`) sigmaAtx
                                                         -- TODO ALSO PROPAGATE DOWNWARDS
                                                      ) us) updateX
      return $ Just (PTerm (f , propagate))





vertexIsPoint :: Vert -> Point -> [PTerm] -> Solving s [PTerm]
vertexIsPoint x a pts = do
  -- pts' <- filterM (\(PTerm (f , sigma)) -> evalPoint f x >>= \b -> return (a == b)) pts

  pts' <- mapM (checkPTerm x a) pts
  return $ catMaybes pts'



comp :: Type -> Solving s [Result]
comp (Type [(Term (a , Tele []) , (Term (b , Tele [])))]) = do
  let gdim = 1
  Cube cube <- gets cube

  let pterms = map (\f -> createPTerm f gdim) cube

  side0 <- vertexIsPoint (Vert [e1]) (Point a) pterms >>= newVar
  side1 <- vertexIsPoint (Vert [e1]) (Point b) pterms >>= newVar
  back <- newVar pterms

  lookupDom side0 >>= trace . show
  lookupDom side1 >>= trace . show
  lookupDom back >>= trace . show

  -- restrict vertices
  verticesAgree [(Vert [e0], Vert [e0])] side0 back
  verticesAgree [(Vert [e0], Vert [e1])] side1 back

  -- sides and back
  -- boundariesAgree 1 e0 1 e0 side0 back
  -- boundariesAgree 1 e0 1 e1 side1 back
  -- subsumed by vertices check in this case...

  return []

-- comp (Type [(k,l), (m,n)]) = do
--   let gdim = 2
--   Cube cube <- gets cube
--   side0 <- newVar $ map (\f -> createPSubst f gdim) cube

--   return []

comp goal = do
  -- let dims = [1..(dim goal)]
  -- sides0 <- mapM (\i -> do
  --                    cb <- getBoundaryC c i False 0
  --                    -- trace $ show i ++ " with boundary " ++ show cb
  --                    (filterM (\ s -> do
  --                                    sb <- getBoundary s (dim c) True
  --                                    -- trace $ show s ++ " has bound " ++ show sb ++ ": " ++ show (sb == cb)
  --                                    return $ sb == cb
  --                                    ) shapes) >>= newVar) dims
  -- sides1 <- mapM (\i -> do
  --                    cb <- getBoundaryC c i True 0
  --                    (filterM (\ s -> do
  --                                    sb <- getBoundary s (dim c) True
  --                                    return $ sb == cb
  --                                    ) shapes) >>= newVar) dims
  -- back <- newVar shapes

  -- trace "DOMAINS BEFORE CONSTRAINTS"
  -- mapM (\s -> lookupDom s >>= \d -> trace $ (dimAsString !! s) ++ "0: " ++ show d) sides0
  -- mapM (\s -> lookupDom s >>= \d -> trace $ (dimAsString !! (s - dim c)) ++ "1: " ++ show d) sides1

  return []




solve :: Solving s [Result]
solve = do
  trace "CUBE"
  Cube cube <- gets cube
  mapM (\(Decl (face , ty)) -> trace $ face ++ " : " ++ show ty) cube

  trace "GOAL"
  goal <- gets goal
  trace $ show goal

  comp goal

  return []
