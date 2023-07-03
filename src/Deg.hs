{-# LANGUAGE FlexibleContexts #-}
module Deg where

import Control.Monad
import qualified Data.Set as Set
import Data.List
import Control.Monad.State
import Data.Ord
import Data.Maybe
import Data.List
import qualified Data.Map as Map
import Data.Map ((!), Map)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Either


import System.Exit
import System.IO.Unsafe

import Prel

import Debug.Trace


type Id = String
type Dim = Int
type IVar = Int
-- type Endpoint = Bool
data Endpoint = I0 | I1
  deriving (Eq, Ord)

instance Show Endpoint where
  show I0 = "0"
  show I1 = "1"

negI I0 = I1
negI I1 = I0

type Restr = (IVar , Endpoint)

data Term = Var Id
          | Deg Term IVar
          | Fill Restr Ty
          | Comp Restr Ty
  deriving (Eq , Show , Ord)

idT :: Id -> Term -- TODO remove from code
idT p = Var p

type Assign = (Restr , Term)

(+>) :: Restr -> Term -> Assign
r +> t = (r , t)

data Ty = Ty Dim [Assign]
  deriving (Eq , Show , Ord)
-- quotient out by reordering of assignments

type Decl = (Id , Ty)
type Cube = [Decl]



tyDim :: Ty -> Dim
tyDim (Ty d _) = d

termDim :: Cube -> Id -> Dim
termDim ctxt p = tyDim (getDef ctxt p)





getDef :: Cube -> Id -> Ty
getDef ctxt name =
  case lookup name ctxt of
    Just face -> face
    Nothing -> error $ "Could not find definition of " ++ name

sideSpec :: Ty -> Restr -> Bool
sideSpec (Ty d fs) f =
  case lookup f fs of
    Just face -> True
    Nothing -> False

getFace :: Ty -> Restr -> Term
getFace (Ty d fs) f =
  case lookup f fs of
    Just face -> face
    Nothing -> error $ "Could not find face " ++ show f


validTy :: Cube -> Ty -> Bool
validTy ctxt (Ty d fs) =
  all (==True)
    [ termFace ctxt t (j-1,e') == termFace ctxt t' (i,e)
      | ((i,e) , t) <- fs , ((j,e') , t') <- fs , i < j ]
  -- & d not exceeded

validTerm :: Cube -> Term -> Bool
validTerm ctxt (Fill f ty) =
  not (sideSpec ty f) && validTy ctxt ty


-- type inference
inferTy :: Cube -> Term -> Ty
inferTy ctxt (Var p) = getDef ctxt p
inferTy ctxt (Deg t i) = let Ty d ty = inferTy ctxt t in
  Ty (d+1) (   [ (j,e) +> Deg (termFace ctxt t (j,e)) (d) | j <- [1..i-1] , e <- [I0,I1] ]
            ++ [ (i,e) +> t | e <- [I0,I1] ]
            ++ [ (j+1,e) +> Deg (termFace ctxt t (j,e)) (d) | j <- [i..d] , e <- [I0,I1] ])
inferTy ctxt (Fill f (Ty d fs)) = Ty d ((f +> (Comp f (Ty (d - 1) fs))) : fs)
inferTy ctxt (Comp f (Ty d fs)) = undefined


termFace :: Cube -> Term -> Restr -> Term
termFace ctxt t = getFace (inferTy ctxt t)


-- Generate terms for domains
restrictions :: Int -> [Restr]
restrictions n = [ (i,e) | i <- [1..n], e <- [I0,I1]]

allVarDeg :: Cube -> Id -> Dim -> [Term]
allVarDeg ctxt p d =
  if termDim ctxt p == d
    then [Var p]
    else [ Deg t j | t <- allVarDeg ctxt p (d-1) , j <- [1..d] ]
  -- there are some terms with the same type -- x<s1><s1> and x<s1><s2>

allDeg :: Cube -> Dim -> [Term]
allDeg ctxt d = nubBy (\t t' -> inferTy ctxt t == inferTy ctxt t') $ concat [ allVarDeg ctxt p d | (p,_) <- ctxt ]
  -- get rid of unnecessary elements here as well?

allFill :: Cube -> Dim -> [Term]
allFill ctxt d =
  let ts = allDeg ctxt (d-1) in
  let restr = restrictions d in
  let pot = do
      ie <- restr
      let jes = delete ie restr
      fs <- mapM (\je -> do
                        t <- ts
                        return (je +> t)) jes
      -- traceShowM tuple
      return $ Fill ie (Ty d fs)
      in
    filter (validTerm ctxt) pot
    -- pot
    --  [ Fill d  ] Fill ie (Ty d fs)

    -- [ [ Fill ie (Ty d )  |  ] | ie <- restr , jes = restr \\ ie , [ (jes +> t) | je <- jes , t <- allDeg ] ]



-- Examples
paths :: Cube
paths = [
    ("x" , Ty 0 [])
  , ("y" , Ty 0 [])
  , ("z" , Ty 0 [])
  , ("p" , Ty 1 [(1,I0) +> idT "x" , (1,I1) +> idT "y"])
  , ("q" , Ty 1 [(1,I0) +> idT "y" , (1,I1) +> idT "z"])
  -- , ("pqfill" , Ty 2 [(1,I0) +> Var "p" , (1,I1) +> Var "q" , (2,I0) +> Var "p" , (2,I1) +> Var "q"])
      ]

invGoal = Ty 1 [ (1,I0) +> Var "y"
               , (1,I1) +> Var "x"
                      ]

invFill = Fill (2 , I1) (Ty 2 [
                        (1,I0) +> idT "p"
                      , (1,I1) +> Deg (Var "x") 1
                      , (2,I0) +> Deg (Var "x") 1
                      ])

pFill = Fill (1,I0) (Ty 2 [
                        (1,I1) +> Deg (Var "y") 1
                      , (2,I0) +> Deg (Var "y") 1
                      , (2,I1) +> Var "p"
                      ])
qFill = Fill (1,I1) (Ty 2 [
                        (1,I0) +> Deg (Var "y") 1
                      , (2,I0) +> Deg (Var "y") 1
                      , (2,I1) +> Var "q"
                      ])

orGoal = Ty 2 [ (1,I0) +> Var "p"
              , (1,I1) +> Deg (Var "y") 1
              , (2,I0) +> Var "p"
              , (2,I1) +> Deg (Var "y") 1
                        ]

andGoal = Ty 2 [ (1,I0) +> Deg (Var "x") 1
               , (1,I1) +> Var "p"
               , (2,I0) +> Deg (Var "x") 1
               , (2,I1) +> Var "p"
                          ]

pqpq = Ty 2 [ (1,I0) +> Var "p"
            , (1,I1) +> Var "q"
            , (2,I0) +> Var "p"
            , (2,I1) +> Var "q"
                      ]



-- Composition solver

type Solving s a = StateT (SEnv s) [] a
data Domain = Solv [Term] | Open
  deriving (Show, Eq)

type CVar = Restr
data CVarInfo a = CVarInfo { delayedConstraints :: Solving a (), values :: Domain }

data SEnv s =
  SEnv { ctxt :: Cube
       , goal :: Ty
       , dir :: Restr -- ????
       , open :: [CVar]
       , varMap :: Map CVar (CVarInfo s)
       }


lookupDef :: Id -> Solving s Ty
lookupDef name = do
  c <- gets ctxt
  return $ getDef c name



findComposition :: Cube -> Ty -> Maybe Term
findComposition ctxt goal =
  listToMaybe $ evalStateT runCS (SEnv ctxt goal (tyDim goal + 1, I1) [] Map.empty)

  -- let fixed = map Side (getCompFaces goal) in -- TODO
  -- let nocont = [] in -- TODO
  -- let free = map Side (getFreeFaces goal) in
  -- let couldbe = Back : (((map Side (restrictions (dim goal)) \\ fixed) \\ nocont) \\ free) in
  -- case (catMaybes $
  --       (map (\uns -> run fixed (nocont ++ uns)) (incps free))
  --       ++ (map (\uns -> run fixed (nocont ++ free ++ uns)) (tail (incps couldbe)))
  --      ) of
  --   ((Comp t):_) -> Just $ Comp (insertFillers ctxt goal t)
  --   [] -> Nothing

  --   where
  --     run :: [CVar] -> [CVar] -> Maybe Term
      -- run fixed open = listToMaybe $ evalStateT (runCS) (SEnv ctxt goal fixed open Map.empty)


runCS :: Solving s Term
runCS = do
  ty@(Ty d fs) <- gets goal
  ctxt <- gets ctxt
  (gi,ge) <- gets dir
  open <- gets open

  -- traceM $ "RUNNING WITH OPEN SIDES " ++ show open

  let pterms = allDeg ctxt d ++ allFill ctxt d
  let faceInd = restrictions d ++ [(gi,negI ge)]

  sides <- mapM (\f@(i,e) ->
                   -- if f `elem` open
                   --   then newCVar f Open
                   if i == gi
                     then newCVar f (Solv pterms)
                     else
                      let t = getFace ty f in do
                        -- case t of
                        --   -- TODO insert fills more subtly -- sometimes not possible to unfold all comps
                        --   Comp f fs -> newCVar f (Solv [Fill f fs])
                        --   _ -> do
                            let ts = filter (\pt -> termFace ctxt pt (gi-1,ge) == t) pterms
                            -- v <- newCVar f (Solv (ts ++ [pfill,qfill]))
                            v <- newCVar f (Solv ts)
                            -- singleConstraint (d,I1) f [t]
                            return v
            )
        faceInd

  domains <- mapM (\s -> lookupDom s >>= \r -> return (s , r)) sides
  traceM $ "AFTER INIT\n" ++ concatMap ((++ "\n") . show) domains ++ "END"

  mapM_ (\(f,g) -> boundaryConstraint f g) [ (f,g) | (f:ys) <- tails faceInd, g <- ys , fst f /= fst g ]

  domains <- mapM (\s -> lookupDom s >>= \r -> return (s , r)) sides
  traceM $ "AFTER SIDE\n" ++ concatMap ((++ "\n") . show) domains ++ "END"

  ress <- mapM (\f -> getSol f >>= \s -> return (f,s)) sides
  mapM traceShowM ress
  -- traceShowM ress
  -- return $ Comp (Box ress resb)

  return undefined
  -- perhaps return just list here? decide whether included in comp in parent function?



singleConstraint :: Restr -> CVar -> [Term] -> Solving s ()
singleConstraint f c hs = addConstraint c $ do
  ctxt <- gets ctxt
  cd <- lookupDom c
  -- traceM $ show (pss) ++ "@" ++ show ie ++ " constrained to " ++ show hs
  case cd of
    Solv ts -> do
      let ts' = filter (\t -> termFace ctxt t f `elem` hs) ts
      when (ts' /= ts) $ update c (Solv ts')

boundaryConstraint :: Restr -> Restr -> Solving s ()
boundaryConstraint = addBinaryConstraint $ \c d -> do
  ctxt <- gets ctxt
  -- traceM $ "MATCH " ++ show c ++ " WITH " ++ show d

  -- TODO DOES THE BELOW MAKE SENSE?
  let (cf , df) = if fst c < fst d
        then (c , (fst d - 1 , snd d))
        else ((fst c - 1 , snd c) , d)

  -- traceM $ "   AT " ++ show cf ++ " AND " ++ show df

  cd <- lookupDom c
  dd <- lookupDom d

  case (cd , dd) of
    (Solv ts , Solv ss) -> do
      let tsf = map (\t -> termFace ctxt t df) ts
      let ssg = map (\t -> termFace ctxt t cf) ss
      -- traceShowM tsf
      -- traceShowM ssg

      let hs = tsf `intersect` ssg
      -- traceShowM hs

      let ts' = filter (\t -> termFace ctxt t df `elem` hs) ts
      let ss' = filter (\t -> termFace ctxt t cf `elem` hs) ss

      -- traceShowM ts'
      -- traceShowM ss'

      when (ts' /= ts) $ update c (Solv ts')
      when (ss' /= ss) $ update d (Solv ss')

-- boundaryConstraint :: Restr -> Restr -> CVar -> CVar -> Solving s ()
-- boundaryConstraint f g = addBinaryConstraint $ \c d -> do
--   ctxt <- gets ctxt
--   cd <- lookupDom c
--   dd <- lookupDom d
--   traceM $ "MATCH " ++ show c ++ "@" ++ show f ++ " WITH " ++ show d ++ "@" ++ show g

--   case (cd , dd) of
--     (Solv ts , Solv ss) -> do
--       let tsf = map (\t -> termFace ctxt t f) ts
--       let ssg = map (\t -> termFace ctxt t g) ss
--       traceShowM tsf
--       traceShowM ssg

--       let hs = tsf `intersect` ssg
--       traceShowM hs

--       let ts' = filter (\t -> termFace ctxt t f `elem` hs) ts
--       let ss' = filter (\t -> termFace ctxt t f `elem` hs) ss

--       when (ts' /= ts) $ update c (Solv ts')
--       when (ss' /= ss) $ update c (Solv ss')

-- DOMAIN AND CONSTRAINT MANAGEMENT

newCVar :: CVar -> Domain -> Solving s CVar
newCVar v domain = do
    v `isOneOf` domain
    return v
    where
        x `isOneOf` domain =
            modify $ \s ->
                let vm = varMap s
                    vi = CVarInfo {
                        delayedConstraints = return (),
                        values = domain}
                in
                s { varMap = Map.insert x vi vm }

lookupDom :: CVar -> Solving s Domain
lookupDom x = do
    s <- get
    return . values $ varMap s ! x

update :: CVar -> Domain -> Solving s ()
update x i = do
    s <- get
    let vm = varMap s
    let vi = vm ! x
    put $ s { varMap = Map.insert x (vi { values = i }) vm }
    delayedConstraints vi

addConstraint :: CVar -> Solving s () -> Solving s ()
addConstraint x constraint = do
    s <- get
    let vm = varMap s
    let vi = vm ! x
    let cs = delayedConstraints vi
    put $ s { varMap =
        Map.insert x (vi { delayedConstraints = cs >> constraint }) vm }

type BinaryConstraint s = CVar -> CVar -> Solving s ()
addBinaryConstraint :: BinaryConstraint s -> BinaryConstraint s
addBinaryConstraint f x y = do
    let constraint  = f x y
    constraint
    addConstraint x constraint
    addConstraint y constraint

getSol :: CVar -> Solving s Term
getSol var = do
  val <- lookupDom var
  case val of
    Solv ts -> do
      sol <- lift ts
      update var (Solv [sol])
      return sol
    Open -> return undefined

