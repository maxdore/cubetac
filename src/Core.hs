{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Core where

import Control.Monad
import Control.Monad.State
import Data.List
import qualified Data.Map as Map
import Data.Map ((!), Map)
import Data.Maybe
import Data.Ord

import Prel

import System.Exit
import System.IO.Unsafe
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

toBool :: Endpoint -> Bool
toBool I0 = False
toBool I1 = True

type Restr = (IVar , Endpoint)


-- This type class specifies which functions rulesets need to export
class (Eq r , Show r , Eq w , Show w) => Rs r w where
  -- dim :: Ctxt r w -> r -> Dim
  infer :: Ctxt r w -> Term r w -> r -> Ty r w
  -- allSTerms :: Ctxt r w -> Dim -> [Term r w]
  -- all rulesets which we consider allow for degeneracies:
  deg :: Ctxt r w -> Term r w -> IVar -> Term r w

  allPTerms :: Ctxt r w -> Dim -> [Term r w]

  unfold :: w -> [r]
  combine :: [r] -> w

-- class Rs r w => Wrapper w r where
--   allPTerms :: Ctxt r w -> Dim -> [Term w]
--   unfold :: w -> [r]



data Term r w = Var Id
          | Fill Restr (Ty r w) -- Fill dir ty means fill type ty in direction dir
          | Comp Restr (Ty r w)
          | App (Term r w) r -- Apply term constructors of ruleset
          | PApp (Term r w) w -- Apply collection of term constructors
  deriving (Eq , Show)





-- Syntactic sugar to allow writing (1,I0) +> t
(+>) :: Restr -> Term r w -> Face r w
r +> t = (r , t)

type Face r w = (Restr , Term r w)
data Ty r w = Ty Dim [Face r w]

-- To check equality of types we need to order their faces
instance Rs r w => Eq (Ty r w) where
  Ty d fs ==  Ty d' fs' = d == d' && sortOn fst fs == sortOn fst fs'

-- Print faces of a cube on different lines and indented
instance (Show r , Show w) => Show (Ty r w) where
  show (Ty d fs) = "Ty " ++ show d ++ " [\n  " ++
    intercalate ", " (map
                      (\(f,t) -> show f ++ " +> " ++ concatMap (\l ->  "   " ++ l ++ "\n") (lines (show t)))
                      (sortOn fst fs))
    ++ "]"

type Decl r w = (Id , Ty r w)
type Ctxt r w = [Decl r w]




-- Basic operations on the types
idDim :: Ctxt r w -> Id -> Dim
idDim c p = let Ty d _ = getDef c p in d

termDim :: Rs r w => Ctxt r w -> Term r w -> Dim
termDim c t = let Ty n _ = inferTy c t in n

getDef :: Ctxt r w -> Id -> Ty r w
getDef c name =
  case lookup name c of
    Just face -> face
    Nothing -> error $ "Could not find definition of " ++ name

simpleTerm :: Rs r w => Term r w -> Bool
simpleTerm (Var _) = True
simpleTerm (App _ _) = True
simpleTerm _ = False

getFace :: Rs r w => Ty r w -> Restr -> Term r w
getFace ty@(Ty _ fs) f =
  case lookup f fs of
    Just face -> face
    Nothing -> error $ "Could not find face " ++ show f ++ " of " ++ show ty

termFace :: Rs r w => Ctxt r w -> Term r w -> Restr -> Term r w
termFace c t = getFace (inferTy c t)

ptermFace :: Rs r w => Ctxt r w -> Term r w -> Restr -> [Term r w]
ptermFace c (PApp t ss) ie = map (\s -> termFace c (App t s) ie) (unfold ss)
ptermFace c t ie = [termFace c t ie]


restrPTerm :: Rs r w => Ctxt r w -> Term r w -> Restr -> [Term r w] -> Maybe (Term r w)
restrPTerm c (PApp t ss) ie hs =
  let ss' = filter (\s -> termFace c (App t s) ie `elem` hs) (unfold ss) in
    if null ss'
      then Nothing
      else Just (PApp t (combine ss'))
restrPTerm c t ie hs = if termFace c t ie `elem` hs then Just t else Nothing


sideSpec :: Ty r w -> Restr -> Bool
sideSpec (Ty _ fs) f = isJust (lookup f fs)

validTy :: Rs r w => Ctxt r w -> Ty r w -> Bool
validTy c (Ty _ fs) =
  and [ termFace c t (j-1,e') == termFace c t' (i,e)
           | ((i,e) , t) <- fs , ((j,e') , t') <- fs , i < j ]
  -- TODO check also no faces assigned multiple times & that d not exceeded

validTerm :: Rs r w => Ctxt r w -> Term r w -> Bool
validTerm c (Fill f ty) = not (sideSpec ty f) && validTy c ty

computeOpenBoundary :: Rs r w => Ctxt r w -> Ty r w -> Restr -> Ty r w
computeOpenBoundary c (Ty d fs) (oi,oe) =
  -- trace ("COMPUTE BOUNDARY OF " ++ show (Ty d fs) ++ " AT " ++ show (oi,oe)) $
  Ty (d-1) [ (if i < oi then i else i-1 , e) +> termFace c t (if oi > i then oi-1 else oi,oe) | ((i,e),t) <- fs , i /= oi ]

-- Type inference
inferTy :: Rs r w => Ctxt r w -> Term r w -> Ty r w
inferTy c (Var p) = getDef c p
inferTy _ (Fill o (Ty d fs)) = Ty d ((o +> Comp o (Ty d fs)) : fs)
inferTy c (Comp o ty) = computeOpenBoundary c ty o
inferTy c (App t r) = infer c t r


-- Generate terms for domains
restrictions :: Int -> [Restr]
restrictions n = [ (i,e) | i <- [1..n], e <- [I0,I1]]


allIds :: Ctxt r w -> Dim -> [Term r w]
allIds c d = [ Var p | (p , Ty d' _) <- c , d == d'  ]

-- All basic fillers for a given dimension
allFill :: Rs r w => Ctxt r w -> Dim -> [Term r w]
allFill c d =
  let ts = allIds c (d-1) in -- ++ allSTerms c (d-1) in
  let restr = restrictions d in
    filter (validTerm c) (do
      ie <- restr
      let jes = delete ie restr
      fs <- mapM (\je -> do
                        t <- ts
                        return (je +> t)) jes
      return $ Fill ie (Ty d fs))

unspecSides :: Ty r w -> [Restr]
unspecSides (Ty d fs) = restrictions d \\ (map fst fs)

fillable :: Rs r w => Ctxt r w -> Ty r w -> [Term r w]
fillable c ty@(Ty d fs)
  | length fs == 2*d = [ Fill cd (Ty d fs') | f@(_ , Comp cd (Ty _ gs)) <- fs , let fs' = delete f fs , gs == fs'  ]
  -- | length fs < 2*d = let sol = map (\s -> Fill s ty) (unspecSides ty) in
  --     trace ("CAN FILL " ++ show sol) sol
  | length fs == 2*d - 1 = let sol = Fill (head (unspecSides ty)) ty in
      if validTerm c sol && all (simpleTerm . snd) fs
        -- then trace ("CAN FILL " ++ show sol) [sol]
        then [sol]
        else []
  | otherwise = []

-- MAIN SOLVER LOGIC

-- Call the composition solver by iteratively deepening box level
findComp :: Rs r w => Ctxt r w -> Ty r w -> Term r w
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

findCompBounded :: Rs r w => Ctxt r w -> Ty r w -> Int -> [Term r w]
findCompBounded c ty 0 = constrOpenComp c ty [[]] 0
findCompBounded c ty@(Ty d _) depth =
  let sides = restrictions d ++ [(d + 1, I0)] in
  constrOpenComp c ty (incpsordbound (depth+1) sides) depth
    where
    -- Generates the powerset of a list in ascending cardinality

-- opens specifies which combinations of sides of the cube can be left open
constrOpenComp :: Rs r w => Ctxt r w -> Ty r w -> [[Restr]] -> Int -> [Term r w]
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

type Solving s a w r = StateT (SEnv s w r) [] a
type Domain r w = [Term r w]

type CVar = Restr
data CVarInfo a w r = CVarInfo { delayedConstraints :: Solving a () w r, values :: Domain r w}

data SEnv s w r =
  SEnv { ctxt :: Ctxt r w
       , goal :: Ty r w
       , dir :: Restr -- in which direction do we want a comp
       , open :: [CVar] --  the sides of the cubes that should be left open
       , varMap :: Map CVar (CVarInfo s w r)
       }

lookupDef :: Id -> Solving s (Ty r w) w r
lookupDef name = do
  c <- gets ctxt
  return $ getDef c name

runCS :: Rs r w => Solving s [Face r w] w r
runCS = do
  ty@(Ty d fs) <- gets goal
  c <- gets ctxt
  (gi,ge) <- gets dir
  ope <- gets open

  -- traceM $ "SOLVE IN " ++ show (gi,ge) ++ " FOR " ++ show ty ++ " WITH OPEN SIDES " ++ show ope
  traceM $ "OPE " ++ show ope

  -- TODO have option for turning on inserting fillers
  -- let pterms = allIds c d ++ allSTerms c d ++ allFill c d
  let pterms = [ Fill cd t | (_ , Comp cd t) <- fs ] ++ allIds c d ++ allPTerms c d
  let solv = (restrictions d ++ [(gi,negI ge)]) \\ ope

  sides <- mapM (\f@(i,_) ->
                      if i == gi || not (sideSpec ty f)
                        then newCVar f pterms -- if the side of the goal is not specified, we fill it in any way we want
                        else do
                          let gf = getFace ty f
                          v <- newCVar f (catMaybes $ map (\t -> restrPTerm c t (gi-1,ge) [gf]) pterms)
                          -- (filter (\pt -> gf `elem` ptermFace c pt (gi-1,ge)) pterms)
                          -- singleConstraint f v [gf] -- TODO SHOULD BE HERE!
                          return v
            )
        solv

  domains <- mapM (\s -> lookupDom s >>= \r -> return (s , r)) sides
  traceM $ "AFTER INIT\n" ++ concatMap ((++ "\n") . show) domains ++ "END"

  mapM_ (uncurry boundaryConstraint) [ (f,g) | (f:ys) <- tails solv, g <- ys , fst f /= fst g ]

  domains <- mapM (\s -> lookupDom s >>= \r -> return (s , r)) sides
  traceM $ "AFTER SIDE\n" ++ concatMap ((++ "\n") . show) domains ++ "END"

  mapM (\f -> getSol f >>= \s -> return (f,s)) sides
  -- unsafePerformIO $ die "ASD"


-- Constraint management

singleConstraint :: Rs r w => Restr -> CVar -> [Term r w] -> Solving s () w r
singleConstraint f cv hs = addConstraint cv $ do
  c <- gets ctxt
  ts <- lookupDom cv
  let ts' = catMaybes $ map (\t -> restrPTerm c t f hs) ts
  -- let ts' = filter (\t -> termFace c t f `elem` hs) ts
  when (ts' /= ts) $ update cv ts'

boundaryConstraint :: Rs r w => Restr -> Restr -> Solving s () w r
boundaryConstraint = addBinaryConstraint $ \cv dv -> do
  c <- gets ctxt
  let (cf , df) = if fst cv < fst dv
        then (cv , (fst dv - 1 , snd dv))
        else ((fst cv - 1 , snd cv) , dv)

  ts <- lookupDom cv
  ss <- lookupDom dv
  let tsf = concatMap (\t -> ptermFace c t df) ts
  let ssg = concatMap (\t -> ptermFace c t cf) ss

  let hs = tsf `intersect` ssg

  guard (not (null hs))

  -- let ts' = filter (\t -> termFace c t df `elem` hs) ts
  -- let ss' = filter (\t -> termFace c t cf `elem` hs) ss
  let ts' = catMaybes $ map (\t -> restrPTerm c t df hs) ts
  let ss' = catMaybes $ map (\t -> restrPTerm c t cf hs) ss

  guard (not (null ts'))
  guard (not (null ss'))

  when (ts' /= ts) $ update cv ts'
  when (ss' /= ss) $ update dv ss'

newCVar :: CVar -> Domain r w -> Solving s CVar w r
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

lookupDom :: CVar -> Solving s (Domain r w) w r
lookupDom x = do
    s <- get
    return . values $ varMap s ! x

update :: CVar -> Domain r w -> Solving s () w r
update x i = do
    s <- get
    let vm = varMap s
    let vi = vm ! x
    put $ s { varMap = Map.insert x (vi { values = i }) vm }
    delayedConstraints vi

addConstraint :: CVar -> Solving s () w r -> Solving s () w r
addConstraint x constraint = do
    s <- get
    let vm = varMap s
    let vi = vm ! x
    let cs = delayedConstraints vi
    put $ s { varMap =
        Map.insert x (vi { delayedConstraints = cs >> constraint }) vm }

type BinaryConstraint s w r = CVar -> CVar -> Solving s () w r
addBinaryConstraint :: BinaryConstraint s w r -> BinaryConstraint s w r
addBinaryConstraint f x y = do
    let constraint  = f x y
    constraint
    addConstraint x constraint
    addConstraint y constraint

getSol ::  Rs r w => CVar -> Solving s (Term r w) w r
getSol var = do
  ts <- lookupDom var
  case ts of
    (PApp t ss : _) -> do -- TODO WHAT ABOUT THE REST OF THE SOLUTIONS?
      sol <- lift (map (App t) (unfold ss))
      update var [sol]
      return sol
    t -> return (head t)


-- Examples

tinv :: Rs r w => Ctxt r w -> Term r w -> Term r w
tinv c t =
  Comp (2, I1) (Ty (termDim c t + 1) [
                     (1,I0) +> t
                   , (1,I1) +> deg c (termFace c t (1,I0)) 1
                   , (2,I0) +> deg c (termFace c t (1,I0)) 1 ])

tcomp :: Rs r w => Ctxt r w -> Term r w -> Term r w -> Term r w
tcomp c t t' = -- TODO CHECK IF COMPOSABLE
  Comp (2, I1) (Ty (termDim c t + 1) [
                     (1,I0) +> deg c (termFace c t (1,I0)) 1
                   , (1,I1) +> t'
                   , (2,I0) +> t ])

twop :: Rs r w => Ctxt r w
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

invFill , pFill , qFill , pqComp , pqFill :: Rs r w => Term r w
invFill = Fill (2 , I1) (Ty 2 [
                        (1,I0) +> Var "p"
                      , (1,I1) +> deg twop (Var "x") 1
                      , (2,I0) +> deg twop (Var "x") 1
                      ])

pFill = Fill (1,I0) (Ty 2 [
                        (1,I1) +> deg twop (Var "y") 1
                      , (2,I0) +> deg twop (Var "y") 1
                      , (2,I1) +> Var "p"
                      ])
qFill = Fill (1,I1) (Ty 2 [
                        (1,I0) +> deg twop (Var "y") 1
                      , (2,I0) +> deg twop (Var "y") 1
                      , (2,I1) +> Var "q"
                      ])

pqComp = Comp (2,I1) (Ty 2 [
                        (1,I0) +> deg twop (Var "x") 1
                      , (1,I1) +> Var "q"
                      , (2,I0) +> Var "p"
                           ])

pqFill = Fill (2,I1) (Ty 2 [
                        (1,I0) +> deg twop (Var "x") 1
                      , (1,I1) +> Var "q"
                      , (2,I0) +> Var "p"
                           ])

orGoal , andGoal , pqpq :: Rs r w => Ty r w
orGoal = Ty 2 [ (1,I0) +> Var "p"
              , (1,I1) +> deg twop (Var "y") 1
              , (2,I0) +> Var "p"
              , (2,I1) +> deg twop (Var "y") 1
                        ]

andGoal = Ty 2 [ (1,I0) +> deg twop (Var "x") 1
               , (1,I1) +> Var "p"
               , (2,I0) +> deg twop (Var "x") 1
               , (2,I1) +> Var "p"
                          ]

pqpq = Ty 2 [ (1,I0) +> Var "p"
            , (1,I1) +> Var "q"
            , (2,I0) +> Var "p"
            , (2,I1) +> Var "q"
                      ]

prefl , reflp :: Rs r w => Term r w
prefl = Comp (2,I1) (Ty 2 [
                      (1,I0) +> deg twop (Var "x") 1
                    , (1,I1) +> deg twop (Var "y") 1
                    , (2,I0) +> Var "p"
                        ])

reflp = Comp (2,I1) (Ty 2 [
                      (1,I0) +> deg twop (Var "x") 1
                    , (1,I1) +> Var "p"
                    , (2,I0) +> deg twop (Var "x") 1
                        ])

unitl , unitr :: Rs r w => Ty r w
unitr = Ty 2 [ (1,I0) +> prefl
             , (1,I1) +> Var "p"
             , (2,I0) +> deg twop (Var "x") 1
             , (2,I1) +> deg twop (Var "y") 1
             ]


unitl = Ty 2 [ (1,I0) +> reflp
             , (1,I1) +> Var "p"
             , (2,I0) +> deg twop (Var "x") 1
             , (2,I1) +> deg twop (Var "y") 1
             ]

threep :: Ctxt r w
threep = [
    ("w" , Ty 0 [])
  , ("x" , Ty 0 [])
  , ("y" , Ty 0 [])
  , ("z" , Ty 0 [])
  , ("p" , Ty 1 [(1,I0) +> Var "w" , (1,I1) +> Var "x"])
  , ("q" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "y"])
  , ("r" , Ty 1 [(1,I0) +> Var "y" , (1,I1) +> Var "z"])
      ]

assocback, assocright , assoc , assoc2 , assocOr , assocAnd :: Rs r w => Ty r w
assocback = Ty 2 [ (1,I0) +> tcomp threep (Var "p") (Var "q")
                 , (1,I1) +> Var "p"
                 , (2,I0) +> deg threep (Var "w") 1
             ]

assocright = Ty 2 [ (1,I0) +> Var "r"
                  , (1,I1) +> tcomp threep (Var "q") (Var "r")
                  -- , (2,I0) +> tinv threep (Var "q")
                  , (2,I1) +> deg threep (Var "z") 1
             ]

assoc = Ty 2 [ (1,I0) +> tcomp threep (tcomp threep (Var "p") (Var "q")) (Var "r")
             , (1,I1) +> tcomp threep (Var "p") (tcomp threep (Var "q") (Var "r"))
             , (2,I0) +> deg threep (Var "w") 1
             , (2,I1) +> deg threep (Var "z") 1
             ]

assoc2 = Ty 2 [ (1,I0) +> tcomp threep (Var "p") (tcomp threep (Var "q") (Var "r"))
              , (1,I1) +> tcomp threep (tcomp threep (Var "p") (Var "q")) (Var "r")
              , (2,I0) +> deg threep (Var "w") 1
              , (2,I1) +> deg threep (Var "z") 1
              ]

assocOr = Ty 2 [ (1,I0) +> tcomp threep (Var "p") (tcomp threep (Var "q") (Var "r"))
               , (1,I1) +>  deg threep (Var "z") 1
               , (2,I0) +> tcomp threep (tcomp threep (Var "p") (Var "q")) (Var "r")
               , (2,I1) +> deg threep (Var "z") 1
              ]

assocAnd = Ty 2 [ (1,I0) +>  deg threep (Var "w") 1
                , (1,I1) +> tcomp threep (Var "p") (tcomp threep (Var "q") (Var "r"))
                , (2,I0) +> deg threep (Var "w") 1
                , (2,I1) +> tcomp threep (tcomp threep (Var "p") (Var "q")) (Var "r")
              ]

threep' :: Rs r w => Ctxt r w
threep' = [
    ("x" , Ty 0 [])
  , ("p" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "x"])
  , ("q" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "x"])
  , ("r" , Ty 1 [(1,I0) +> Var "x" , (1,I1) +> Var "x"])
      ]

assoc' :: Rs r w => Ty r w
assoc' = Ty 2 [
    (1,I0) +> tcomp threep' (tcomp threep' (Var "p") (Var "q")) (Var "r")
  , (1,I1) +> tcomp threep' (Var "p") (tcomp threep' (Var "q") (Var "r"))
  , (2,I0) +> deg threep' (Var "x") 1
  , (2,I1) +> deg threep' (Var "x") 1
      ]


eqsq :: Rs r w => Ctxt r w
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


eqsqfill = Fill (1,I1) (Ty 2 [
                       (1,I0) +> Var "q"
                     , (2,I1) +> Var "p"
              ])
