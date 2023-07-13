{-# LANGUAGE FlexibleContexts #-}
module Core where

import Control.Monad
import Control.Monad.State
import Data.List
import qualified Data.Map as Map
import Data.Map ((!), Map)
import Data.Maybe
import Data.Ord

import Debug.Trace
-- trace _ = id
-- traceM _ = return ()


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

type Restr = (IVar , Endpoint)


-- This type class specifies which functions rulesets need to export
class (Eq r , Show r) => Rs r where
  dim :: Ctxt r -> r -> Dim
  infer :: Ctxt r -> r -> Ty r
  allSTerms :: Ctxt r -> Dim -> [Term r]
  -- all rulesets which we consider allow for degeneracies:
  deg :: Term r -> IVar -> Term r

data Term r = Var Id
          | Fill Restr (Ty r) -- Fill dir ty means fill type ty in direction dir
          | Comp Restr (Ty r)
          | STerm r -- the constructor for terms of the ruleset
  deriving (Eq , Show)

-- Syntactic sugar to allow writing (1,I0) +> t
(+>) :: Restr -> Term r -> Face r
r +> t = (r , t)

type Face a = (Restr , Term a)
data Ty a = Ty Dim [Face a]

-- To check equality of types we need to order their faces
instance Rs r => Eq (Ty r) where
  Ty d fs ==  Ty d' fs' = d == d' && sortOn fst fs == sortOn fst fs'

-- Print faces of a cube on different lines and indented
instance Show a => Show (Ty a) where
  show (Ty d fs) = "Ty " ++ show d ++ " [\n  " ++
    intercalate ", " (map
                      (\(f,t) -> show f ++ " +> " ++ concatMap (\l ->  "   " ++ l ++ "\n") (lines (show t)))
                      (sortOn fst fs))
    ++ "]"

type Decl a = (Id , Ty a)
type Ctxt a = [Decl a]



-- Basic operations on the types
idDim :: Ctxt r -> Id -> Dim
idDim c p = let Ty d _ = getDef c p in d

termDim :: Rs r => Ctxt r -> Term r -> Dim
termDim c (Var p) = idDim c p
termDim _ (Fill _ (Ty d _)) = d
termDim _ (Comp _ (Ty d _)) = d-1
termDim c (STerm t) = dim c t

getDef :: Ctxt r -> Id -> Ty r
getDef c name =
  case lookup name c of
    Just face -> face
    Nothing -> error $ "Could not find definition of " ++ name

getFace :: Rs r => Ty r -> Restr -> Term r
getFace ty@(Ty _ fs) f =
  case lookup f fs of
    Just face -> face
    Nothing -> error $ "Could not find face " ++ show f ++ " of " ++ show ty

termFace :: Rs r => Ctxt r -> Term r -> Restr -> Term r
termFace c t = getFace (inferTy c t)

sideSpec :: Ty r -> Restr -> Bool
sideSpec (Ty _ fs) f = isJust (lookup f fs)

validTy :: Rs r => Ctxt r -> Ty r -> Bool
validTy c (Ty _ fs) =
  and [ termFace c t (j-1,e') == termFace c t' (i,e)
           | ((i,e) , t) <- fs , ((j,e') , t') <- fs , i < j ]
  -- TODO check also no faces assigned multiple times & that d not exceeded

validTerm :: Rs r => Ctxt r -> Term r -> Bool
validTerm c (Fill f ty) = not (sideSpec ty f) && validTy c ty

computeOpenBoundary :: Rs r => Ctxt r -> Ty r -> Restr -> Ty r
computeOpenBoundary c (Ty d fs) (oi,oe) =
  -- trace ("COMPUTE BOUNDARY OF " ++ show (Ty d fs) ++ " AT " ++ show (oi,oe)) $
  Ty (d-1) [ (if i < oi then i else i-1 , e) +> termFace c t (if oi > i then oi-1 else oi,oe) | ((i,e),t) <- fs , i /= oi ]

-- Type inference
inferTy :: Rs r => Ctxt r -> Term r -> Ty r
inferTy c (Var p) = getDef c p
inferTy _ (Fill o (Ty d fs)) = Ty d ((o +> Comp o (Ty d fs)) : fs)
inferTy c (Comp o ty) = computeOpenBoundary c ty o
inferTy c (STerm t) = infer c t


-- Generate terms for domains
restrictions :: Int -> [Restr]
restrictions n = [ (i,e) | i <- [1..n], e <- [I0,I1]]


allIds :: Ctxt r -> Dim -> [Term r]
allIds c d = [ Var p | (p , Ty d' _) <- c , d == d'  ]

-- All basic fillers for a given dimension
allFill :: Rs r => Ctxt r -> Dim -> [Term r]
allFill c d =
  let ts = allIds c (d-1) ++ allSTerms c (d-1) in
  let restr = restrictions d in
    filter (validTerm c) (do
      ie <- restr
      let jes = delete ie restr
      fs <- mapM (\je -> do
                        t <- ts
                        return (je +> t)) jes
      return $ Fill ie (Ty d fs))

unspecSides :: Ty r -> [Restr]
unspecSides (Ty d fs) = restrictions d \\ (map fst fs)

fillable :: Rs r => Ctxt r -> Ty r -> [Term r]
fillable c ty@(Ty d fs)
  | length fs == 2*d = [ Fill cd (Ty d fs') | f@(_ , Comp cd (Ty _ gs)) <- fs , let fs' = delete f fs , gs == fs'  ]
  -- | length fs < 2*d = let sol = map (\s -> Fill s ty) (unspecSides ty) in
  --     trace ("CAN FILL " ++ show sol) sol
  | length fs == 2*d - 1 = let sol = Fill (head (unspecSides ty)) ty in
      if validTerm c sol
        -- then trace ("CAN FILL " ++ show sol) [sol]
        then [sol]
        else []
                        | otherwise = []

-- MAIN SOLVER LOGIC

-- Call the composition solver by iteratively deepening box level
findComp :: Rs r => Ctxt r -> Ty r -> Term r
findComp c ty = head (concatMap (findCompBounded c ty) [0..])

ps :: [a] -> [[a]]
ps = filterM (const [True, False])

psord :: [a] -> [[a]]
psord = concat . map permutations . ps

incps :: [a] -> [[a]]
incps = sortBy (comparing length) . ps

incpsbound :: Int -> [a] -> [[a]]
incpsbound d = (filter (\s -> length s <= d)) . incps

incpsord :: [a] -> [[a]]
incpsord = sortBy (comparing length) . psord

incpsordbound :: Int -> [a] -> [[a]]
incpsordbound d = (filter (\s -> length s <= d)) . incpsord

findCompBounded :: Rs r => Ctxt r -> Ty r -> Int -> [Term r]
findCompBounded c ty 0 = constrOpenComp c ty [[]] 0
findCompBounded c ty@(Ty d _) depth =
  let sides = restrictions d ++ [(d + 1, I0)] in
  constrOpenComp c ty (incpsordbound (depth+1) sides) depth
    where
    -- Generates the powerset of a list in ascending cardinality

-- opens specifies which combinations of sides of the cube can be left open
constrOpenComp :: Rs r => Ctxt r -> Ty r -> [[Restr]] -> Int -> [Term r]
constrOpenComp c ty@(Ty d _) opens depth = do
  let cdir = (d + 1, I1)
  ope <- opens
  sol <- evalStateT runCS (SEnv c ty cdir ope Map.empty)
  full <- foldM
    (\s o -> do
        -- traceM $ "TRYING TO FILL " ++ show o
        let gobdy = if sideSpec ty o then [(d + 1 , I1) +> Fill cdir ty] else []
        let wty = Ty (d + 1) (s ++ gobdy)
        let fty = computeOpenBoundary c wty o
        -- traceM $ "TRYING TO FILL " ++ show o ++ " : " ++ show fty
        fsol <- fillable c fty ++ findCompBounded c fty (depth - 1)
        return $ s ++ [o +> fsol]
        )
    sol
    ope
  return $ Comp cdir (Ty (d + 1) full)



-- CSP SOLVER

type Solving s a r = StateT (SEnv s r) [] a
type Domain a = [Term a]

type CVar = Restr
data CVarInfo a r = CVarInfo { delayedConstraints :: Solving a () r, values :: Domain r }

data SEnv s r =
  SEnv { ctxt :: Ctxt r
       , goal :: Ty r
       , dir :: Restr -- in which direction do we want a comp
       , open :: [CVar] --  the sides of the cubes that should be left open
       , varMap :: Map CVar (CVarInfo s r)
       }

lookupDef :: Id -> Solving s (Ty r) r
lookupDef name = do
  c <- gets ctxt
  return $ getDef c name

runCS :: Rs r => Solving s [Face r] r
runCS = do
  ty@(Ty d fs) <- gets goal
  c <- gets ctxt
  (gi,ge) <- gets dir
  ope <- gets open

  -- traceM $ "SOLVE IN " ++ show (gi,ge) ++ " FOR " ++ show ty ++ " WITH OPEN SIDES " ++ show ope
  traceM $ "OPE " ++ show ope

  -- TODO have option for turning on inserting fillers
  let pterms = allIds c d ++ allSTerms c d ++ [ Fill cd t | (_ , Comp cd t) <- fs ] -- ++ allFill c d
  let solv = (restrictions d ++ [(gi,negI ge)]) \\ ope

  sides <- mapM (\f@(i,_) ->
                      if i == gi || not (sideSpec ty f)
                        then newCVar f pterms -- if the side of the goal is not specified, we fill it in any way we want
                        else newCVar f (filter (\pt -> termFace c pt (gi-1,ge) == getFace ty f) pterms)
            )
        solv

  domains <- mapM (\s -> lookupDom s >>= \r -> return (s , r)) sides
  traceM $ "AFTER INIT\n" ++ concatMap ((++ "\n") . show) domains ++ "END"

  mapM_ (uncurry boundaryConstraint) [ (f,g) | (f:ys) <- tails solv, g <- ys , fst f /= fst g ]

  domains <- mapM (\s -> lookupDom s >>= \r -> return (s , r)) sides
  traceM $ "AFTER SIDE\n" ++ concatMap ((++ "\n") . show) domains ++ "END"

  mapM (\f -> getSol f >>= \s -> return (f,s)) sides



-- Constraint management

singleConstraint :: Rs r => Restr -> CVar -> [Term r] -> Solving s () r
singleConstraint f cv hs = addConstraint cv $ do
  c <- gets ctxt
  ts <- lookupDom cv
  let ts' = filter (\t -> termFace c t f `elem` hs) ts
  when (ts' /= ts) $ update cv ts'

boundaryConstraint :: Rs r => Restr -> Restr -> Solving s () r
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

newCVar :: CVar -> Domain r -> Solving s CVar r
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

lookupDom :: CVar -> Solving s (Domain r) r
lookupDom x = do
    s <- get
    return . values $ varMap s ! x

update :: CVar -> Domain r -> Solving s () r
update x i = do
    s <- get
    let vm = varMap s
    let vi = vm ! x
    put $ s { varMap = Map.insert x (vi { values = i }) vm }
    delayedConstraints vi

addConstraint :: CVar -> Solving s () r -> Solving s () r
addConstraint x constraint = do
    s <- get
    let vm = varMap s
    let vi = vm ! x
    let cs = delayedConstraints vi
    put $ s { varMap =
        Map.insert x (vi { delayedConstraints = cs >> constraint }) vm }

type BinaryConstraint s r = CVar -> CVar -> Solving s () r
addBinaryConstraint :: BinaryConstraint s r -> BinaryConstraint s r
addBinaryConstraint f x y = do
    let constraint  = f x y
    constraint
    addConstraint x constraint
    addConstraint y constraint

getSol :: CVar -> Solving s (Term r) r
getSol var = do
  ts <- lookupDom var
  sol <- lift ts
  update var [sol]
  return sol


-- Examples

tinv :: Rs r => Ctxt r -> Term r -> Term r
tinv c t =
  Comp (2, I1) (Ty (termDim c t + 1) [
                     (1,I0) +> t
                   , (1,I1) +> deg (termFace c t (1,I0)) 1
                   , (2,I0) +> deg (termFace c t (1,I0)) 1 ])

tcomp :: Rs r => Ctxt r -> Term r -> Term r -> Term r
tcomp c t t' = -- TODO CHECK IF COMPOSABLE
  Comp (2, I1) (Ty (termDim c t + 1) [
                     (1,I0) +> deg (termFace c t (1,I0)) 1
                   , (1,I1) +> t'
                   , (2,I0) +> t ])

twop :: Rs r => Ctxt r
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

invFill , pFill , qFill , pqComp :: Rs r => Term r
invFill = Fill (2 , I1) (Ty 2 [
                        (1,I0) +> Var "p"
                      , (1,I1) +> deg (Var "x") 1
                      , (2,I0) +> deg (Var "x") 1
                      ])

pFill = Fill (1,I0) (Ty 2 [
                        (1,I1) +> deg (Var "y") 1
                      , (2,I0) +> deg (Var "y") 1
                      , (2,I1) +> Var "p"
                      ])
qFill = Fill (1,I1) (Ty 2 [
                        (1,I0) +> deg (Var "y") 1
                      , (2,I0) +> deg (Var "y") 1
                      , (2,I1) +> Var "q"
                      ])

pqComp = Comp (2,I1) (Ty 2 [
                        (1,I0) +> deg (Var "x") 1
                      , (1,I1) +> Var "q"
                      , (2,I0) +> Var "p"
                           ])

orGoal , andGoal , pqpq :: Rs r => Ty r
orGoal = Ty 2 [ (1,I0) +> Var "p"
              , (1,I1) +> deg (Var "y") 1
              , (2,I0) +> Var "p"
              , (2,I1) +> deg (Var "y") 1
                        ]

andGoal = Ty 2 [ (1,I0) +> deg (Var "x") 1
               , (1,I1) +> Var "p"
               , (2,I0) +> deg (Var "x") 1
               , (2,I1) +> Var "p"
                          ]

pqpq = Ty 2 [ (1,I0) +> Var "p"
            , (1,I1) +> Var "q"
            , (2,I0) +> Var "p"
            , (2,I1) +> Var "q"
                      ]

prefl , reflp :: Rs r => Term r
prefl = Comp (2,I1) (Ty 2 [
                      (1,I0) +> deg (Var "x") 1
                    , (1,I1) +> deg (Var "y") 1
                    , (2,I0) +> Var "p"
                        ])

reflp = Comp (2,I1) (Ty 2 [
                      (1,I0) +> deg (Var "x") 1
                    , (1,I1) +> Var "p"
                    , (2,I0) +> deg (Var "x") 1
                        ])

unitl , unitr :: Rs r => Ty r
unitr = Ty 2 [ (1,I0) +> prefl
             , (1,I1) +> Var "p"
             , (2,I0) +> deg (Var "x") 1
             , (2,I1) +> deg (Var "y") 1
             ]


unitl = Ty 2 [ (1,I0) +> reflp
             , (1,I1) +> Var "p"
             , (2,I0) +> deg (Var "x") 1
             , (2,I1) +> deg (Var "y") 1
             ]

threep :: Ctxt r
threep = [
    ("w" , Ty 0 [])
  , ("x" , Ty 0 [])
  , ("y" , Ty 0 [])
  , ("z" , Ty 0 [])
  , ("p" , Ty 1 [(1,I0) +> Var "w" , (1,I1) +> Var "x"])
  , ("q" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "y"])
  , ("r" , Ty 1 [(1,I0) +> Var "y" , (1,I1) +> Var "z"])
      ]

assocback, assocright , assoc , assoc2 , assocOr , assocAnd :: Rs r => Ty r
assocback = Ty 2 [ (1,I0) +> tcomp threep (Var "p") (Var "q")
                 , (1,I1) +> Var "p"
                 , (2,I0) +> deg (Var "w") 1
             ]

assocright = Ty 2 [ (1,I0) +> Var "r"
                  , (1,I1) +> tcomp threep (Var "q") (Var "r")
                  , (2,I1) +> deg (Var "z") 1
             ]

assoc = Ty 2 [ (1,I0) +> tcomp threep (tcomp threep (Var "p") (Var "q")) (Var "r")
             , (1,I1) +> tcomp threep (Var "p") (tcomp threep (Var "q") (Var "r"))
             , (2,I0) +> deg (Var "w") 1
             , (2,I1) +> deg (Var "z") 1
             ]

assoc2 = Ty 2 [ (1,I0) +> tcomp threep (Var "p") (tcomp threep (Var "q") (Var "r"))
              , (1,I1) +> tcomp threep (tcomp threep (Var "p") (Var "q")) (Var "r")
              , (2,I0) +> deg (Var "w") 1
              , (2,I1) +> deg (Var "z") 1
              ]

assocOr = Ty 2 [ (1,I0) +> tcomp threep (Var "p") (tcomp threep (Var "q") (Var "r"))
               , (1,I1) +>  deg (Var "z") 1
               , (2,I0) +> tcomp threep (tcomp threep (Var "p") (Var "q")) (Var "r")
               , (2,I1) +> deg (Var "z") 1
              ]

assocAnd = Ty 2 [ (1,I0) +>  deg (Var "w") 1
                , (1,I1) +> tcomp threep (Var "p") (tcomp threep (Var "q") (Var "r"))
                , (2,I0) +> deg (Var "w") 1
                , (2,I1) +> tcomp threep (tcomp threep (Var "p") (Var "q")) (Var "r")
              ]

threep' :: Rs r => Ctxt r
threep' = [
    ("x" , Ty 0 [])
  , ("p" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "x"])
  , ("q" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "x"])
  , ("r" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "x"])
      ]

assoc' :: Rs r => Ty r
assoc' = Ty 2 [
    (1,I0) +> tcomp threep' (tcomp threep' (Var "p") (Var "q")) (Var "r")
  , (1,I1) +> tcomp threep' (Var "p") (tcomp threep' (Var "q") (Var "r"))
  , (2,I0) +> deg (Var "x") 1
  , (2,I1) +> deg (Var "x") 1
      ]


eqsq :: Rs r => Ctxt r
eqsq = [
    ("x" , Ty 0 [])
  , ("p" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "x"])
  , ("q" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "x"])
  -- , ("alpha" , Ty 2 [ (1,I0) +> Var "p"
  --                   , (1,I1) +> Var "q"
  --                   -- , (2,I0) +> deg (Var "x") 1
  --                   -- , (2,I1) +> deg (Var "x") 1
  --                   ])
    ]

eqsqinv = Ty 2 [ (1,I0) +> Var "q"
              , (1,I1) +> Var "p"
              -- , (2,I0) +> deg (Var "x") 1
              -- , (2,I1) +> deg (Var "x") 1
              ]
