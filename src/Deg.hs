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
type IVar = Int

-- Endpoint datatype for nice printing
data Endpoint = I0 | I1
  deriving (Eq, Show , Ord)

negI :: Endpoint -> Endpoint
negI I0 = I1
negI I1 = I0

-- Term language
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

-- Print faces on different lines and indented
instance Show Ty where
  show (Ty d fs) = "Ty " ++ show d ++ " [\n  " ++
    intercalate ", " (map
                      (\(f,t) -> show f ++ " +> " ++ concatMap (\l ->  "   " ++ l ++ "\n") (lines (show t)))
                      (sortOn fst fs))
    ++ "]"

type Decl = (Id , Ty)
type Cube = [Decl]


-- Basic operations on the types
idDim :: Cube -> Id -> Dim
idDim c p = let Ty d _ = getDef c p in d

termDim :: Cube -> Term -> Dim
termDim c (Var p) = idDim c p
termDim c (Deg t _) = 1 + termDim c t
termDim _ (Fill _ (Ty d _)) = d
termDim _ (Comp _ (Ty d _)) = d-1

getDef :: Cube -> Id -> Ty
getDef c name =
  case lookup name c of
    Just face -> face
    Nothing -> error $ "Could not find definition of " ++ name


getFace :: Ty -> Restr -> Term
getFace (Ty _ fs) f =
  case lookup f fs of
    Just face -> face
    Nothing -> error $ "Could not find face " ++ show f

sideSpec :: Ty -> Restr -> Bool
sideSpec (Ty _ fs) f = isJust (lookup f fs)


validTy :: Cube -> Ty -> Bool
validTy c (Ty _ fs) =
  and [ termFace c t (j-1,e') == termFace c t' (i,e)
           | ((i,e) , t) <- fs , ((j,e') , t') <- fs , i < j ]
  -- TODO check also no faces assigned multiple times & that d not exceeded

validTerm :: Cube -> Term -> Bool
validTerm c (Fill f ty) = not (sideSpec ty f) && validTy c ty


computeOpenBoundary :: Cube -> Ty -> Restr -> Ty
computeOpenBoundary c (Ty d fs) (oi,oe) =
  Ty (d-1) [ (if i < oi then i else i-1 , e) +> termFace c t (if oi > i then oi-1 else oi,oe) | ((i,e),t) <- fs , i /= oi ]

-- type inference
inferTy :: Cube -> Term -> Ty
inferTy c (Var p) = getDef c p
inferTy c (Deg t i) = let Ty d _ = inferTy c t in
  Ty (d+1) (   [ (j,e) +> Deg (termFace c t (j,e)) d | j <- [1..i-1] , e <- [I0,I1] ]
            ++ [ (i,e) +> t | e <- [I0,I1] ]
            ++ [ (j+1,e) +> Deg (termFace c t (j,e)) d | j <- [i..d] , e <- [I0,I1] ])
inferTy _ (Fill o (Ty d fs)) = Ty d ((o +> Comp o (Ty d fs)) : fs)
inferTy c (Comp o ty) = computeOpenBoundary c ty o

termFace :: Cube -> Term -> Restr -> Term
termFace c t = getFace (inferTy c t)


-- Generate terms for domains
restrictions :: Int -> [Restr]
restrictions n = [ (i,e) | i <- [1..n], e <- [I0,I1]]

allVarDeg :: Cube -> Id -> Dim -> [Term]
allVarDeg c p d | idDim c p > d = []
                   | idDim c p == d = [Var p]
                   | otherwise =
                       nubBy (\t t' -> inferTy c t == inferTy c t')
                       [ Deg t j | t <- allVarDeg c p (d-1) , j <- [1..d] ]

allDeg :: Cube -> Dim -> [Term]
allDeg c d = concat [ allVarDeg c p d | (p,_) <- c ]

allFill :: Cube -> Dim -> [Term]
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

constrOpenComp :: Cube -> Ty -> [[Restr]] -> Int -> [Term]
constrOpenComp c ty@(Ty d _) opens fuel = do
  let comp = (d + 1, I1)
  ope <- opens
  sol <- evalStateT runCS (SEnv c ty comp ope Map.empty)
  full <- foldM
    (\s o -> do
        -- traceM "ALERT"
        -- traceShowM s
        let wty = Ty (d + 1) (s ++ [(d + 1 , I1) +> Fill comp ty])
        -- traceShowM wty
        let fty = computeOpenBoundary c wty o
        -- traceShowM fty
        -- unsafePerformIO (die "asd")
        fsol <- findCompBounded c fty (fuel - 1)
        -- traceShowM $ "FOUND" ++ show fsol
        return $ s ++ [o +> fsol]
        )
    sol
    ope

  return $ Comp comp (Ty (d + 1) full)


findCompBounded :: Cube -> Ty -> Int -> [Term]
findCompBounded c ty 0 = constrOpenComp c ty [[]] 0

findCompBounded c ty@(Ty d _) fuel =
  let comp = (d + 1, I1) in
  let sides = delete comp $ restrictions (d + 1) in
  constrOpenComp c ty (incps sides) fuel
    where
    incps :: [a] -> [[a]]
    incps = sortBy (comparing length) . filterM (const [True, False])



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
  c <- gets ctxt
  (gi,ge) <- gets dir
  ope <- gets open

  -- traceM $ "SOLVE IN " ++ show (gi,ge) ++ " FOR " ++ show ty ++ " WITH OPEN SIDES " ++ show open

  let pterms = allDeg c d ++ allFill c d ++ [ Fill cd t | (_ , Comp cd t) <- fs ]
  let faceInd = restrictions d ++ [(gi,negI ge)]

  sides <- mapM (\f@(i,_) ->
                      if i == gi || not (sideSpec ty f)
                        then newCVar f pterms
                        else newCVar f (filter (\pt -> termFace c pt (gi-1,ge) == getFace ty f) pterms)
            )
        (faceInd \\ ope)

  -- domains <- mapM (\s -> lookupDom s >>= \r -> return (s , r)) sides
  -- traceM $ "AFTER INIT\n" ++ concatMap ((++ "\n") . show) domains ++ "END"

  -- TODO just closed sides here?
  mapM_ (uncurry boundaryConstraint) [ (f,g) | (f:ys) <- tails faceInd, g <- ys , fst f /= fst g ]

  -- domains <- mapM (\s -> lookupDom s >>= \r -> return (s , r)) sides
  -- traceM $ "AFTER SIDE\n" ++ concatMap ((++ "\n") . show) domains ++ "END"

  mapM (\f -> getSol f >>= \s -> return (f,s)) sides



singleConstraint :: Restr -> CVar -> [Term] -> Solving s ()
singleConstraint f cv hs = addConstraint cv $ do
  c <- gets ctxt
  ope <- gets open
  -- traceM $ show (pss) ++ "@" ++ show ie ++ " constrained to " ++ show hs
  unless (cv `elem` ope) $ do
    ts <- lookupDom cv
    let ts' = filter (\t -> termFace c t f `elem` hs) ts
    when (ts' /= ts) $ update cv ts'

boundaryConstraint :: Restr -> Restr -> Solving s ()
boundaryConstraint = addBinaryConstraint $ \cv dv -> do
  c <- gets ctxt
  ope <- gets open
  -- traceM $ "MATCH " ++ show c ++ " WITH " ++ show d

  -- TODO DOES THE BELOW MAKE SENSE?
  let (cf , df) = if fst cv < fst dv
        then (cv , (fst dv - 1 , snd dv))
        else ((fst cv - 1 , snd cv) , dv)

  -- traceM $ "   AT " ++ show cf ++ " AND " ++ show df

  when (cv `notElem` ope && dv `notElem` ope) $ do
      ts <- lookupDom cv
      ss <- lookupDom dv
      let tsf = map (\t -> termFace c t df) ts
      let ssg = map (\t -> termFace c t cf) ss
      -- traceShowM tsf
      -- traceShowM ssg

      let hs = tsf `intersect` ssg
      -- traceShowM hs

      let ts' = filter (\t -> termFace c t df `elem` hs) ts
      let ss' = filter (\t -> termFace c t cf `elem` hs) ss

      -- traceShowM ts'
      -- traceShowM ss'

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



-- Examples

tcomp :: Cube -> Term -> Term -> Term
tcomp c t t' = -- TODO CHECK IF COMPOSABLE
  Comp (2, I1) (Ty (termDim c t + 1) [
                     (1,I0) +> Deg (termFace c t (1,I0)) 1
                   , (1,I1) +> t'
                   , (2,I0) +> t ])



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
