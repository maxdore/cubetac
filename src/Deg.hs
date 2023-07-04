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
data Endpoint = I0 | I1
  deriving (Eq, Show , Ord)

negI I0 = I1
negI I1 = I0

type Restr = (IVar , Endpoint)

data Term = Var Id
          | Deg Term IVar
          | Fill Restr Ty
          | Comp Restr Ty
  deriving (Eq , Show)

type Face = (Restr , Term)

(+>) :: Restr -> Term -> Face
r +> t = (r , t)

data Ty = Ty Dim [Face]

instance Show Ty where
  -- show (Ty d fs) = "Ty " ++ show d ++ "\n" ++ concatMap (\(f,t) -> "   " ++ show f ++ " +> " ++ show t ++ "\n") (sortOn fst fs)
  show (Ty d fs) = "Ty " ++ show d ++ " [\n  " ++
    (concat . intersperse ", ") (map (\(f,t) -> show f ++ " +> " ++ concatMap (\l ->  "   " ++ l ++ "\n") (lines (show t))) (sortOn fst fs))
    ++ "]"

instance Eq Ty where
  Ty d fs ==  Ty d' fs' = d == d' && sortOn fst fs == sortOn fst fs'

type Decl = (Id , Ty)
type Cube = [Decl]



tyDim :: Ty -> Dim
tyDim (Ty d _) = d

idDim :: Cube -> Id -> Dim
idDim ctxt p = tyDim (getDef ctxt p)

termDim :: Cube -> Term -> Dim
termDim ctxt (Var p) = idDim ctxt p
termDim ctxt (Deg t _) = 1 + termDim ctxt t
termDim ctxt (Fill _ (Ty d _)) = d
termDim ctxt (Comp _ (Ty d _)) = d-1



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


computeOpenBoundary :: Cube -> Ty -> Restr -> Ty
computeOpenBoundary ctxt (Ty d fs) (oi,oe) =
  Ty (d-1) [ (if i < oi then i else i-1 , e) +> termFace ctxt t (if oi > i then oi-1 else oi,oe) | ((i,e),t) <- fs , i /= oi ]

-- type inference
inferTy :: Cube -> Term -> Ty
inferTy ctxt (Var p) = getDef ctxt p
inferTy ctxt (Deg t i) = let Ty d ty = inferTy ctxt t in
  Ty (d+1) (   [ (j,e) +> Deg (termFace ctxt t (j,e)) (d) | j <- [1..i-1] , e <- [I0,I1] ]
            ++ [ (i,e) +> t | e <- [I0,I1] ]
            ++ [ (j+1,e) +> Deg (termFace ctxt t (j,e)) (d) | j <- [i..d] , e <- [I0,I1] ])

inferTy ctxt (Fill o (Ty d fs)) = Ty d ((o +> (Comp o (Ty d fs))) : fs)

inferTy ctxt (Comp o ty) = computeOpenBoundary ctxt ty o
  -- Ty (d-1) [ (if i < oi then i else i-1 , e) +> termFace ctxt t (if oi > i then oi-1 else oi,oe) | ((i,e),t) <- fs , i /= oi ]


termFace :: Cube -> Term -> Restr -> Term
termFace ctxt t = getFace (inferTy ctxt t)


-- Generate terms for domains
restrictions :: Int -> [Restr]
restrictions n = [ (i,e) | i <- [1..n], e <- [I0,I1]]

allVarDeg :: Cube -> Id -> Dim -> [Term]
allVarDeg ctxt p d | idDim ctxt p > d = []
                   | idDim ctxt p == d = [Var p]
                   | otherwise =
                       nubBy (\t t' -> inferTy ctxt t == inferTy ctxt t')
                       [ Deg t j | t <- allVarDeg ctxt p (d-1) , j <- [1..d] ]

allDeg :: Cube -> Dim -> [Term]
allDeg ctxt d = concat [ allVarDeg ctxt p d | (p,_) <- ctxt ]

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
      return $ Fill ie (Ty d fs)
      in
    filter (validTerm ctxt) pot





-- Composition solver

type Solving s a = StateT (SEnv s) [] a
type Domain = [Term]

type CVar = Restr
data CVarInfo a = CVarInfo { delayedConstraints :: Solving a (), values :: Domain }

data SEnv s =
  SEnv { ctxt :: Cube
       , goal :: Ty
       , dir :: Restr
       , open :: [CVar]
       , varMap :: Map CVar (CVarInfo s)
       }


lookupDef :: Id -> Solving s Ty
lookupDef name = do
  c <- gets ctxt
  return $ getDef c name



-- findComposition :: Cube -> Ty -> Maybe Term
-- findComposition ctxt goal =
--   case catMaybes (map run (incps sides)) of
--     (t:_) -> Just t
--     [] -> Nothing

--     where
--     comp = (tyDim goal + 1, I1)
--     sides = delete comp $ restrictions (tyDim goal + 1)
--     run :: [CVar] -> Maybe Term
--     run open = listToMaybe $ evalStateT (runCS) (SEnv ctxt goal comp open Map.empty)

  -- listToMaybe $ evalStateT runCS (SEnv ctxt goal (tyDim goal + 1, I1) [] Map.empty)


constrOpenComp :: Cube -> Ty -> [[Restr]] -> Int -> [Term]
constrOpenComp ctxt goal opens fuel = do
  let comp = (tyDim goal + 1, I1)
  ope <- opens
  sol <- evalStateT runCS (SEnv ctxt goal comp ope Map.empty)
  full <- foldM
    (\s o -> do
        -- traceM "ALERT"
        -- traceShowM s
        let wty = (Ty (tyDim goal + 1) (s ++ [(tyDim goal + 1 , I1) +> Fill comp goal]))
        -- traceShowM wty
        let fty = computeOpenBoundary ctxt wty o
        -- traceShowM fty
        -- unsafePerformIO (die "asd")
        fsol <- findCompBounded ctxt fty (fuel - 1)
        -- traceShowM $ "FOUND" ++ show fsol
        return $ s ++ [o +> fsol]
        )
    sol
    ope

  return $ Comp comp (Ty (tyDim goal + 1) full)


findCompBounded :: Cube -> Ty -> Int -> [Term]
findCompBounded ctxt goal 0 = constrOpenComp ctxt goal [[]] 0

findCompBounded ctxt goal fuel =
  let comp = (tyDim goal + 1, I1) in
  let sides = delete comp $ restrictions (tyDim goal + 1) in
  constrOpenComp ctxt goal (incps sides) fuel



-- test = foldM (\s o -> do
--         fsol <- findCompBounded paths (Ty 2 [ (1,I0) +>    Deg (Var "x") 1
--                                             , (1,I1) +>    Var "p"
--                                             , (2,I0) +>    Deg (Var "x") 1
--                                             , (2,I1) +>    Var "p"]) 0
--         return $ s ++ [o +> fsol]
--         )
--     [((1,I0), Fill (2,I1) (Ty 2 [
--                           (1,I0) +>    Deg (Var "x") 1
--                         , (1,I1) +>    Var "p"
--                         , (2,I0) +>    Deg (Var "x") 1
--                         ])
--     ),((2,I0),Deg (Deg (Var "x") 1) 1),((2,I1),Deg (Var "p") 1),((3,I0),Deg (Deg (Var "x") 1) 1)]
--     [(1,I1)]



runCS :: Solving s [Face]
runCS = do
  ty@(Ty d fs) <- gets goal
  ctxt <- gets ctxt
  (gi,ge) <- gets dir
  open <- gets open

  -- traceM $ "SOLVE IN " ++ show (gi,ge) ++ " FOR " ++ show ty ++ " WITH OPEN SIDES " ++ show open

  let pterms = allDeg ctxt d ++ allFill ctxt d
  let faceInd = restrictions d ++ [(gi,negI ge)]

  sides <- mapM (\f@(i,e) ->
                      if i == gi || not (sideSpec ty f)
                        then newCVar f pterms
                        else newCVar f (filter (\pt -> termFace ctxt pt (gi-1,ge) == getFace ty f) pterms)
            )
        (faceInd \\ open)

  -- domains <- mapM (\s -> lookupDom s >>= \r -> return (s , r)) sides
  -- traceM $ "AFTER INIT\n" ++ concatMap ((++ "\n") . show) domains ++ "END"

  -- TODO just closed sides here?
  mapM_ (\(f,g) -> boundaryConstraint f g) [ (f,g) | (f:ys) <- tails faceInd, g <- ys , fst f /= fst g ]

  -- domains <- mapM (\s -> lookupDom s >>= \r -> return (s , r)) sides
  -- traceM $ "AFTER SIDE\n" ++ concatMap ((++ "\n") . show) domains ++ "END"

  ress <- mapM (\f -> getSol f >>= \s -> return (f,s)) sides
  -- mapM traceShowM ress
  -- traceShowM ress

  -- return $ Comp (gi,ge) (Ty d ress)
  return ress



singleConstraint :: Restr -> CVar -> [Term] -> Solving s ()
singleConstraint f c hs = addConstraint c $ do
  ctxt <- gets ctxt
  open <- gets open
  -- traceM $ show (pss) ++ "@" ++ show ie ++ " constrained to " ++ show hs
  when (not (c `elem` open)) $ do
    ts <- lookupDom c
    let ts' = filter (\t -> termFace ctxt t f `elem` hs) ts
    when (ts' /= ts) $ update c ts'

boundaryConstraint :: Restr -> Restr -> Solving s ()
boundaryConstraint = addBinaryConstraint $ \c d -> do
  ctxt <- gets ctxt
  open <- gets open
  -- traceM $ "MATCH " ++ show c ++ " WITH " ++ show d

  -- TODO DOES THE BELOW MAKE SENSE?
  let (cf , df) = if fst c < fst d
        then (c , (fst d - 1 , snd d))
        else ((fst c - 1 , snd c) , d)

  -- traceM $ "   AT " ++ show cf ++ " AND " ++ show df

  when (not (c `elem` open) && not (d `elem` open)) $ do
      ts <- lookupDom c
      ss <- lookupDom d
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

      when (ts' /= ts) $ update c ts'
      when (ss' /= ss) $ update d ss'


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
  ts <- lookupDom var
  sol <- lift ts
  update var ([sol])
  return sol



-- Examples
paths :: Cube
paths = [
    ("x" , Ty 0 [])
  , ("y" , Ty 0 [])
  , ("z" , Ty 0 [])
  , ("p" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "y"])
  , ("q" , Ty 1 [(1,I0) +> Var "y" , (1,I1) +> Var "z"])
      ]

invGoal = Ty 1 [ (1,I0) +> Var "y"
               , (1,I1) +> Var "x"
                      ]

invFill = Fill (2 , I1) (Ty 2 [
                        (1,I0) +> Var "p"
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

pqComp = Comp (2,I1) (Ty 2 [
                        (1,I0) +> Deg (Var "x") 1
                      , (1,I1) +> Var "q"
                      , (2,I0) +> Var "p"
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

prefl = Comp (2,I1) (Ty 2 [
                      (1,I0) +> Deg (Var "x") 1
                    , (1,I1) +> Deg (Var "y") 1
                    , (2,I0) +> Var "p"
                        ])

unitr = Ty 2 [ (1,I0) +> prefl
             , (1,I1) +> Var "p"
             , (2,I0) +> Deg (Var "x") 1
             , (2,I1) +> Deg (Var "y") 1
             ]

reflp = Comp (2,I1) (Ty 2 [
                      (1,I0) +> Deg (Var "x") 1
                    , (1,I1) +> Var "p"
                    , (2,I0) +> Deg (Var "x") 1
                        ])

unitl = Ty 2 [ (1,I0) +> reflp
             , (1,I1) +> Var "p"
             , (2,I0) +> Deg (Var "x") 1
             , (2,I1) +> Deg (Var "y") 1
             ]

tcomp :: Cube -> Term -> Term -> Term
tcomp ctxt t t' = -- TODO CHECK IF COMPOSABLE
  Comp (2, I1) (Ty (termDim ctxt t + 1) [
                     (1,I0) +> Deg (termFace ctxt t (1,I0)) 1
                   , (1,I1) +> t'
                   , (2,I0) +> t ])


three :: Cube
three = [
    ("w" , Ty 0 [])
  , ("x" , Ty 0 [])
  , ("y" , Ty 0 [])
  , ("z" , Ty 0 [])
  , ("p" , Ty 1 [(1,I0) +> Var "w" , (1,I1) +> Var "x"])
  , ("q" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "y"])
  , ("r" , Ty 1 [(1,I0) +> Var "y" , (1,I1) +> Var "z"])
      ]

assocback = Ty 2 [ (1,I0) +> tcomp three (Var "p") (Var "q")
                 , (1,I1) +> Var "p"
                 , (2,I0) +> Deg (Var "w") 1
             ]

assocright = Ty 2 [ (1,I0) +> Var "r"
                  , (1,I1) +> tcomp three (Var "q") (Var "r")
                  , (2,I1) +> Deg (Var "z") 1
             ]

assoc = Ty 2 [ (1,I0) +> tcomp three (tcomp three (Var "p") (Var "q")) (Var "r")
             , (1,I1) +> tcomp three (Var "p") (tcomp three (Var "q") (Var "r"))
             , (2,I0) +> Deg (Var "w") 1
             , (2,I1) +> Deg (Var "z") 1
             ]
