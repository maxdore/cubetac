{-# LANGUAGE FlexibleContexts #-}
module Deg where

import Control.Monad
import Control.Monad.State
import Data.List
import qualified Data.Map as Map
import Data.Map ((!), Map)
import Data.Maybe
import Data.Ord



-- basic type synonyms
type Id = String
type Dim = Int
type IVar = Int -- De Bruijn indices for variable names

-- Endpoint datatype for nice printing
data Endpoint = I0 | I1
  deriving (Eq, Show , Ord)

negI :: Endpoint -> Endpoint
negI I0 = I1
negI I1 = I0

-- TERM LANGUAGE

type Restr = (IVar , Endpoint)

data Term = Var Id
          | Deg Term IVar
          | Fill Restr Ty -- Fill dir ty means fill type ty in direction dir
          | Comp Restr Ty
  deriving (Eq , Show)

-- Syntactic sugar to allow writing (1,I0) +> t
(+>) :: Restr -> Term -> Face
r +> t = (r , t)

type Face = (Restr , Term)
data Ty = Ty Dim [Face]

-- To check equality of types we need to order their faces
instance Eq Ty where
  Ty d fs ==  Ty d' fs' = d == d' && sortOn fst fs == sortOn fst fs'

-- Print faces of a cube on different lines and indented
instance Show Ty where
  show (Ty d fs) = "Ty " ++ show d ++ " [\n  " ++
    intercalate ", " (map
                      (\(f,t) -> show f ++ " +> " ++ concatMap (\l ->  "   " ++ l ++ "\n") (lines (show t)))
                      (sortOn fst fs))
    ++ "]"

type Decl = (Id , Ty)
type Ctxt = [Decl]


-- Basic operations on the types
idDim :: Ctxt -> Id -> Dim
idDim c p = let Ty d _ = getDef c p in d

termDim :: Ctxt -> Term -> Dim
termDim c (Var p) = idDim c p
termDim c (Deg t _) = 1 + termDim c t
termDim _ (Fill _ (Ty d _)) = d
termDim _ (Comp _ (Ty d _)) = d-1

getDef :: Ctxt -> Id -> Ty
getDef c name =
  case lookup name c of
    Just face -> face
    Nothing -> error $ "Could not find definition of " ++ name

getFace :: Ty -> Restr -> Term
getFace (Ty _ fs) f =
  case lookup f fs of
    Just face -> face
    Nothing -> error $ "Could not find face " ++ show f

termFace :: Ctxt -> Term -> Restr -> Term
termFace c t = getFace (inferTy c t)

sideSpec :: Ty -> Restr -> Bool
sideSpec (Ty _ fs) f = isJust (lookup f fs)

validTy :: Ctxt -> Ty -> Bool
validTy c (Ty _ fs) =
  and [ termFace c t (j-1,e') == termFace c t' (i,e)
           | ((i,e) , t) <- fs , ((j,e') , t') <- fs , i < j ]
  -- TODO check also no faces assigned multiple times & that d not exceeded

validTerm :: Ctxt -> Term -> Bool
validTerm c (Fill f ty) = not (sideSpec ty f) && validTy c ty

computeOpenBoundary :: Ctxt -> Ty -> Restr -> Ty
computeOpenBoundary c (Ty d fs) (oi,oe) =
  Ty (d-1) [ (if i < oi then i else i-1 , e) +> termFace c t (if oi > i then oi-1 else oi,oe) | ((i,e),t) <- fs , i /= oi ]

-- Type inference
inferTy :: Ctxt -> Term -> Ty
inferTy c (Var p) = getDef c p
inferTy c (Deg t i) = let Ty d _ = inferTy c t in
  Ty (d+1) (   [ (j,e) +> Deg (termFace c t (j,e)) d | j <- [1..i-1] , e <- [I0,I1] ]
            ++ [ (i,e) +> t | e <- [I0,I1] ]
            ++ [ (j+1,e) +> Deg (termFace c t (j,e)) d | j <- [i..d] , e <- [I0,I1] ])
inferTy _ (Fill o (Ty d fs)) = Ty d ((o +> Comp o (Ty d fs)) : fs)
inferTy c (Comp o ty) = computeOpenBoundary c ty o


-- Generate terms for domains
restrictions :: Int -> [Restr]
restrictions n = [ (i,e) | i <- [1..n], e <- [I0,I1]]

-- All degeneracies for a given dimension
allVarDeg :: Ctxt -> Id -> Dim -> [Term]
allVarDeg c p d | idDim c p > d = []
                   | idDim c p == d = [Var p]
                   | otherwise =
                       nubBy (\t t' -> inferTy c t == inferTy c t')
                       [ Deg t j | t <- allVarDeg c p (d-1) , j <- [1..d] ]

allDeg :: Ctxt -> Dim -> [Term]
allDeg c d = concat [ allVarDeg c p d | (p,_) <- c ]

-- All basic fillers for a given dimension
allFill :: Ctxt -> Dim -> [Term]
allFill c d =
  let ts = allDeg c (d-1) in
  let restr = restrictions d in
    filter (validTerm c) (do
      ie <- restr
      let jes = delete ie restr
      fs <- mapM (\je -> do
                        t <- ts
                        return (je +> t)) jes
      return $ Fill ie (Ty d fs))





-- MAIN SOLVER LOGIC

-- Call the composition solver by iteratively deepening box level
findComp :: Ctxt -> Ty -> Term
findComp c ty = head (concatMap (findCompBounded c ty) [0..])

findCompBounded :: Ctxt -> Ty -> Int -> [Term]
findCompBounded c ty 0 = constrOpenComp c ty [[]] 0
findCompBounded c ty@(Ty d _) depth =
  let sides = restrictions d ++ [(d + 1, I0)] in
  constrOpenComp c ty (incps sides) depth
    where
    -- Generates the powerset of a list in ascending cardinality
    incps :: [a] -> [[a]]
    incps = sortBy (comparing length) . filterM (const [True, False])

-- opens specifies which combinations of sides of the cube can be left open
constrOpenComp :: Ctxt -> Ty -> [[Restr]] -> Int -> [Term]
constrOpenComp c ty@(Ty d _) opens depth = do
  let cdir = (d + 1, I1)
  ope <- opens
  sol <- evalStateT runCS (SEnv c ty cdir ope Map.empty)
  full <- foldM
    (\s o -> do
        let wty = Ty (d + 1) (s ++ [(d + 1 , I1) +> Fill cdir ty])
        let fty = computeOpenBoundary c wty o
        fsol <- findCompBounded c fty (depth - 1)
        return $ s ++ [o +> fsol]
        )
    sol
    ope
  return $ Comp cdir (Ty (d + 1) full)



-- CSP SOLVER

type Solving s a = StateT (SEnv s) [] a
type Domain = [Term]

type CVar = Restr
data CVarInfo a = CVarInfo { delayedConstraints :: Solving a (), values :: Domain }

data SEnv s =
  SEnv { ctxt :: Ctxt
       , goal :: Ty
       , dir :: Restr -- in which direction do we want a comp
       , open :: [CVar] --  the sides of the cubes that should be left open
       , varMap :: Map CVar (CVarInfo s)
       }

lookupDef :: Id -> Solving s Ty
lookupDef name = do
  c <- gets ctxt
  return $ getDef c name

runCS :: Solving s [Face]
runCS = do
  ty@(Ty d fs) <- gets goal
  c <- gets ctxt
  (gi,ge) <- gets dir
  ope <- gets open

  -- traceM $ "SOLVE IN " ++ show (gi,ge) ++ " FOR " ++ show ty ++ " WITH OPEN SIDES " ++ show open

  let pterms = allDeg c d ++ allFill c d ++ [ Fill cd t | (_ , Comp cd t) <- fs ]
  let faceInd = restrictions d ++ [(gi,negI ge)]

  sides <- mapM (\f@(i,_) ->
                      if i == gi || not (sideSpec ty f)
                        then newCVar f pterms -- if the side of the goal is not specified, we fill it in any way we want
                        else newCVar f (filter (\pt -> termFace c pt (gi-1,ge) == getFace ty f) pterms)
            )
        (faceInd \\ ope)

  -- domains <- mapM (\s -> lookupDom s >>= \r -> return (s , r)) sides
  -- traceM $ "AFTER INIT\n" ++ concatMap ((++ "\n") . show) domains ++ "END"

  mapM_ (uncurry boundaryConstraint) [ (f,g) | (f:ys) <- tails (faceInd \\ ope), g <- ys , fst f /= fst g ]

  -- domains <- mapM (\s -> lookupDom s >>= \r -> return (s , r)) sides
  -- traceM $ "AFTER SIDE\n" ++ concatMap ((++ "\n") . show) domains ++ "END"

  mapM (\f -> getSol f >>= \s -> return (f,s)) sides



-- Constraint management

singleConstraint :: Restr -> CVar -> [Term] -> Solving s ()
singleConstraint f cv hs = addConstraint cv $ do
  c <- gets ctxt
  ts <- lookupDom cv
  let ts' = filter (\t -> termFace c t f `elem` hs) ts
  when (ts' /= ts) $ update cv ts'

boundaryConstraint :: Restr -> Restr -> Solving s ()
boundaryConstraint = addBinaryConstraint $ \cv dv -> do
  c <- gets ctxt
  let (cf , df) = if fst cv < fst dv
        then (cv , (fst dv - 1 , snd dv))
        else ((fst cv - 1 , snd cv) , dv)

  ts <- lookupDom cv
  ss <- lookupDom dv
  let tsf = map (\t -> termFace c t df) ts
  let ssg = map (\t -> termFace c t cf) ss

  let hs = tsf `intersect` ssg

  let ts' = filter (\t -> termFace c t df `elem` hs) ts
  let ss' = filter (\t -> termFace c t cf `elem` hs) ss

  when (ts' /= ts) $ update cv ts'
  when (ss' /= ss) $ update dv ss'

newCVar :: CVar -> Domain -> Solving s CVar
newCVar v dom = do
    v `isOneOf` dom
    return v
    where
        x `isOneOf` dom' =
            modify $ \s ->
                let vm = varMap s
                    vi = CVarInfo {
                        delayedConstraints = return (),
                        values = dom'}
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
  update var [sol]
  return sol



-- EXAMPLES
-- to run solver use findComp function, e.g., prove associativity with
-- > findComp threep assoc

tcomp :: Ctxt -> Term -> Term -> Term
tcomp c t t' = -- TODO CHECK IF COMPOSABLE
  Comp (2, I1) (Ty (termDim c t + 1) [
                     (1,I0) +> Deg (termFace c t (1,I0)) 1
                   , (1,I1) +> t'
                   , (2,I0) +> t ])

twop :: Ctxt
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



threep :: Ctxt
threep = [
    ("w" , Ty 0 [])
  , ("x" , Ty 0 [])
  , ("y" , Ty 0 [])
  , ("z" , Ty 0 [])
  , ("p" , Ty 1 [(1,I0) +> Var "w" , (1,I1) +> Var "x"])
  , ("q" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "y"])
  , ("r" , Ty 1 [(1,I0) +> Var "y" , (1,I1) +> Var "z"])
      ]

assocback = Ty 2 [ (1,I0) +> tcomp threep (Var "p") (Var "q")
                 , (1,I1) +> Var "p"
                 , (2,I0) +> Deg (Var "w") 1
             ]

assocright = Ty 2 [ (1,I0) +> Var "r"
                  , (1,I1) +> tcomp threep (Var "q") (Var "r")
                  , (2,I1) +> Deg (Var "z") 1
             ]

assoc = Ty 2 [ (1,I0) +> tcomp threep (tcomp threep (Var "p") (Var "q")) (Var "r")
             , (1,I1) +> tcomp threep (Var "p") (tcomp threep (Var "q") (Var "r"))
             , (2,I0) +> Deg (Var "w") 1
             , (2,I1) +> Deg (Var "z") 1
             ]

assoc2 = Ty 2 [ (1,I0) +> tcomp threep (Var "p") (tcomp threep (Var "q") (Var "r"))
              , (1,I1) +> tcomp threep (tcomp threep (Var "p") (Var "q")) (Var "r")
              , (2,I0) +> Deg (Var "w") 1
              , (2,I1) +> Deg (Var "z") 1
              ]

assocOr = Ty 2 [ (1,I0) +> tcomp threep (Var "p") (tcomp threep (Var "q") (Var "r"))
               , (1,I1) +>  Deg (Var "z") 1
               , (2,I0) +> tcomp threep (tcomp threep (Var "p") (Var "q")) (Var "r")
               , (2,I1) +> Deg (Var "z") 1
              ]

assocAnd = Ty 2 [ (1,I0) +>  Deg (Var "w") 1
                , (1,I1) +> tcomp threep (Var "p") (tcomp threep (Var "q") (Var "r"))
                , (2,I0) +> Deg (Var "w") 1
                , (2,I1) +> tcomp threep (tcomp threep (Var "p") (Var "q")) (Var "r")
              ]

threep' :: Ctxt
threep' = [
    ("x" , Ty 0 [])
  , ("p" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "x"])
  , ("q" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "x"])
  , ("r" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "x"])
      ]

assoc' = Ty 2 [
    (1,I0) +> tcomp threep' (tcomp threep' (Var "p") (Var "q")) (Var "r")
  , (1,I1) +> tcomp threep' (Var "p") (tcomp threep' (Var "q") (Var "r"))
  , (2,I0) +> Deg (Var "x") 1
  , (2,I1) +> Deg (Var "x") 1
      ]
