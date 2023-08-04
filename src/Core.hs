{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RankNTypes #-}
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

-- import System.Exit
-- import System.IO.Unsafe
-- import Debug.Trace
trace _ = id
traceM _ = return ()
traceShowM _ = return ()


type Id = String
type Dim = Int -- the dimension of a cube
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

predi :: Restr -> Restr
predi (i,e) = (i-1,e)

succi :: Restr -> Restr
succi (i,e) = (i+1,e)

-- When comparing the boundaries of two faces of a cube, we have to adjust
-- de Brujin indices: if i < j, then j is offset by one and vice versa
adji :: Restr -> Restr -> (Restr, Restr)
adji ie je = if fst ie < fst je then (ie,predi je) else (predi ie, je)

-- This type class specifies which functions rulesets need to export
class (Eq r , Show r , Eq w , Show w) => Rs r w where
  infer :: Ctxt r w -> Term r w -> r -> Ty r w
  -- all rulesets which we consider allow for degeneracies:
  deg :: Ctxt r w -> Term r w -> IVar -> Term r w
  allPTerms :: Ctxt r w -> Dim -> [Term r w]
  unfold :: w -> [r]
  combine :: [r] -> w

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
  show (Ty d fs) = "(Ty " ++ show d ++ " [\n  " ++
    intercalate ", " (map
                      (\(f,t) -> show f ++ " +> " ++ concatMap (\l ->  "   " ++ l ++ "\n") (lines (show t)))
                      (sortOn fst fs))
    ++ "])"

type Decl r w = (Id , Ty r w)
type Ctxt r w = [Decl r w]


-- Basic operations on the types
tyDim :: Ty r w -> Dim
tyDim (Ty d _) = d

idDim :: Ctxt r w -> Id -> Dim
idDim c p = tyDim (getDef c p)

termDim :: Rs r w => Ctxt r w -> Term r w -> Dim
termDim c t = tyDim (inferTy c t)

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
-- termFace c t = trace (show t) $ getFace (inferTy c t)
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
  and [ termFace c t (predi je) == termFace c t' ie
           | (ie , t) <- fs , (je , t') <- fs , fst ie < fst je ]
  -- TODO check also no faces assigned multiple times & that d not exceeded

validTerm :: Rs r w => Ctxt r w -> Term r w -> Bool
validTerm c (Fill f ty) = not (sideSpec ty f) && validTy c ty


-- Computes boundary of an unspecified face of a cube
tyFaceBdy :: Rs r w => Ctxt r w -> Ty r w -> Restr -> Ty r w
tyFaceBdy c (Ty d fs) ie =
  -- trace ("COMPUTE BOUNDARY OF " ++ show (Ty d fs) ++ " AT " ++ show ie) $
  Ty (d-1) [ je' +> termFace c t ie' | (je,t) <- fs , fst je /= fst ie ,
                                       let (je',ie') = adji je ie,
                                       sideSpec (inferTy c t) ie' ]


-- compute a subeface that we know to exist in a cube but cannot access directly
-- TODO SOUND? HAVE TO PERMUTE PROBABLY!!!
get2Face :: Rs r w => Ctxt r w -> Ty r w -> (Restr,Restr) -> Term r w
get2Face c ty (ie,je) =
  if fst je < fst ie
    then termFace c (getFace ty je) (predi ie)
    else termFace c (getFace ty (succi je)) ie

-- Given the unspecified sides of a goal and the unspecified sides of a box with
-- that boundary, compute all the possible fillers (which sides of the box are
-- filled and the direction of the filler).
-- Works as follows: if the goal boundary is unspecified, a filler can go in
-- this direction, otherwise fillers come in pairs
possibleFillers :: [Restr] -> [Restr] -> Dim -> [[(Restr,Restr)]]
possibleFillers ogs ofs d =
  let pairs = [ [(f,predi g),(g,f)] | (f:cs) <- tails ofs , g <- cs , fst f /= fst g] in
  reverse $ sortBy (comparing length) $ filter
    (\ss -> length ss == length (nubBy (\r s -> fst r == fst s) ss))
    (map concat (incps (pairs ++ [ [(g,(d,I1))] | g <- ogs , g `elem` ofs ])))

-- Type inference
inferTy :: Rs r w => Ctxt r w -> Term r w -> Ty r w
inferTy c (Var p) = getDef c p
inferTy _ (Fill ie (Ty d fs)) = Ty d ((ie +> Comp ie (Ty d fs)) : fs)
inferTy c (Comp ie ty) = tyFaceBdy c ty ie
inferTy c (App t r) = infer c t r

-- Generate terms for domains
restrictions :: Int -> [Restr]
restrictions n = [ (i,e) | i <- [1..n], e <- [I0,I1]]

dom :: Ty r w -> [Restr]
dom (Ty d fs) = map fst fs

unspec :: Ty r w -> [Restr]
unspec (Ty d fs) = restrictions d \\ map fst fs

allIds :: Ctxt r w -> Dim -> [Term r w]
allIds c d = [ Var p | (p , Ty d' _) <- c , d == d'  ]


-- MAIN SOLVER LOGIC

-- Call the composition solver by iteratively deepening box level
findComp :: Rs r w => Ctxt r w -> Ty r w -> Term r w
findComp c ty = head (concatMap (findCompBounded c ty) [0..])

findCompBounded :: Rs r w => Ctxt r w -> Ty r w -> Int -> [Term r w]
findCompBounded c ty 0 =
  -- trace "DEPTH 0" $
  constrOpenComp c ty [[]] 0
findCompBounded c ty@(Ty d _) depth =
  -- trace ("DEPTH " ++ show depth) $
  let sides = restrictions d ++ [(d + 1, I0)] in
  constrOpenComp c ty (incps sides) depth

-- opens specifies which combinations of sides of the cube can be left open
constrOpenComp :: Rs r w => Ctxt r w -> Ty r w -> [[Restr]] -> Int -> [Term r w]
constrOpenComp c ty@(Ty d _) opens depth = do
  let cdir = (d + 1, I1)
  ope <- opens
  sol <- evalStateT compCSP (mkCompEnv c ty cdir ope)

  let cube = Ty (d + 1) (sol ++ [(d + 1 , I1) +> Fill cdir ty])

  trytofill <- possibleFillers (unspec ty) ope d
  -- traceShowM $ "FILL COMBINATIONS " ++ show trytofill

  fills <- evalStateT fillerCSP (mkFillEnv c cube trytofill)

  let filledsol = sol ++ fills
  let stillope = ope \\ map fst trytofill

  -- traceM $ "FILLED IN SOL " ++ show filledsol

  if (null stillope)
    then return $ Comp cdir (Ty (d + 1) filledsol)
    else do
      rcomps <- foldM
        (\s ie -> do
            let gobdy = if sideSpec ty ie then [(d + 1 , I1) +> Fill cdir ty] else []
            let fty = tyFaceBdy c (Ty (d + 1) (s ++ gobdy)) ie
            fsol <- findCompBounded c fty (depth - 1)
            return $ s ++ [ie +> fsol]
            )
        filledsol
        stillope

      return $ Comp cdir (Ty (d + 1) rcomps)


-- CSP SOLVER

type Solving s a r w v = StateT (SEnv s r w v) [] a
type Domain r w = [Term r w]
data CVarInfo a r w v = CVarInfo { delayedConstraints :: Solving a () r w v , values :: Domain r w}

class Ord v => Cv v where

-- For the comp CSP we are filling sides of the cube
type CVar = Restr
instance Cv CVar where

-- For the fill CSP we are filling sides of sides of the cube
type FVar = (Restr,Restr)
instance Cv FVar where

data SEnv s r w v =
  SEnv { ctxt :: Ctxt r w
       , goal :: Ty r w
       , varMap :: Map v (CVarInfo s r w v)

       -- state variables used for the comp CSP
       , dir :: Restr -- in which direction do we want a comp
       , open :: [CVar] --  the sides of the cubes that should be left open

       -- state variables used for the filler CSP
       , fil :: [FVar] --  the sides of the cubes to be filled and their fill direction
       }

mkCompEnv c ty ie ope = SEnv c ty Map.empty ie ope undefined
mkFillEnv c ty fil = SEnv c ty Map.empty undefined undefined fil


lookupDef :: Id -> Solving s (Ty r w) r w v
lookupDef name = do
  c <- gets ctxt
  return $ getDef c name

newCVar :: Cv v => v -> Domain r w -> Solving s v r w v
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

lookupDom :: Cv v => v -> Solving s (Domain r w) r w v
lookupDom x = do
    s <- get
    return . values $ varMap s ! x

update :: Cv v => v -> Domain r w -> Solving s () r w v
update x i = do
    s <- get
    let vm = varMap s
    let vi = vm ! x
    put $ s { varMap = Map.insert x (vi { values = i }) vm }
    delayedConstraints vi

addConstraint :: Cv v => v -> Solving s () r w v -> Solving s () r w v
addConstraint x constraint = do
    s <- get
    let vm = varMap s
    let vi = vm ! x
    let cs = delayedConstraints vi
    put $ s { varMap =
        Map.insert x (vi { delayedConstraints = cs >> constraint }) vm }

type BinaryConstraint s r w v = Cv v => v -> v -> Solving s () r w v
addBinaryConstraint :: BinaryConstraint s r w v -> BinaryConstraint s r w v
addBinaryConstraint f x y = do
    let constraint  = f x y
    constraint
    addConstraint x constraint
    addConstraint y constraint

getSol :: Cv v =>  Rs r w => v -> Solving s (Term r w) r w v
getSol var = do
  ts <- lookupDom var
  let allsol = concat $ map (\t -> do
           case t of
             PApp t ss -> map (App t) (unfold ss)
             t -> [t]
           ) ts
  sol <- lift allsol
  update var [sol]
  return sol




compCSP :: Rs r w => Solving s [Face r w] r w CVar
compCSP = do
  ty@(Ty d fs) <- gets goal
  c <- gets ctxt
  (gi,ge) <- gets dir
  ope <- gets open

  -- traceM $ "SOLVE IN " ++ show (gi,ge) ++ " FOR " ++ show ty ++ " WITH OPEN SIDES " ++ show ope

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

  -- domains <- mapM (\s -> lookupDom s >>= \r -> return (s , r)) sides
  -- traceM $ "AFTER INIT\n" ++ concatMap ((++ "\n") . show) domains ++ "END"

  mapM_ (uncurry boundaryConstraint) [ (f,g) | (f:ys) <- tails solv, g <- ys , fst f /= fst g ]

  -- domains <- mapM (\s -> lookupDom s >>= \r -> return (s , r)) sides
  -- traceM $ "AFTER SIDE\n" ++ concatMap ((++ "\n") . show) domains ++ "END"

  mapM (\f -> getSol f >>= \s -> return (f,s)) sides



fillerCSP :: Rs r w => Solving s [Face r w] r w FVar
fillerCSP = do
  c <- gets ctxt
  cube <- gets goal
  fil <- gets fil

  if (null fil)
    then return []
    else do
      -- traceM $ "INSERTING FILLERS " ++ show fil ++ " INTO " ++ show cube

      let pterms = allIds c (tyDim cube - 2) ++ allPTerms c (tyDim cube - 2)

      filfs <- concat <$> mapM (\(ie,fdir) -> do
                      let jes = unspec (tyFaceBdy c cube ie) \\ [fdir]
                      mapM (\je -> do
                              let (Ty _ specf) = tyFaceBdy c cube ie
                              let dom = foldr (\(ke,gf) pts ->
                                                catMaybes $ map (\pt -> let (je' , ke') = adji je ke in restrPTerm c pt ke' [termFace c gf je']) pts)
                                              pterms
                                              (filter (\(ke,_) -> fst ke /= (fst je)) specf)
                                        -- TODO also have to repeat this as a constraint to prevent non-conservative rulesets from yielding wrong results!
                              newCVar (ie,je) dom
                            ) jes
                )
            fil

      -- domains <- mapM (\s -> lookupDom s >>= \r -> return (s , r)) filfs
      -- traceM $ "INIT\n" ++ concatMap ((++ "\n") . show) domains ++ "END"

      mapM_ (uncurry termsEqual) [ (c,d) | (c:cs) <- tails filfs , d <- cs , fst (fst c) /= fst (fst d) , fst c == snd d , snd c == ((\(j,e) -> (j-1 , e)) (fst d))  ]

      mapM_ (uncurry compsEqual) [ (c,d) | (c:cs) <- tails fil , d <- cs , fst (fst c) /= fst (fst d) , fst c == snd d , snd c == ((\(j,e) -> (j-1 , e)) (fst d))  ]

      -- domains <- mapM (\s -> flookupDom s >>= \r -> return (s , r)) filfs
      -- traceM $ "AFTER MATCH\n" ++ concatMap ((++ "\n") . show) domains ++ "END"

      mapM_ (uncurry fboundaryConstraint) [ (c,d) | (c:cs) <- tails filfs , d <- cs , fst c == fst d , fst (snd c) /= fst (snd d) ]

      -- domains <- mapM (\s -> flookupDom s >>= \r -> return (s , r)) filfs
      -- traceM $ "AFTER INTERNAL BOUNDARIES\n" ++ concatMap ((++ "\n") . show) domains ++ "END"

      psol <- mapM (\(ie,fdir) -> do
                      sides <- mapM (\je -> getSol (ie,je) >>= \t -> return (je , t)) (unspec (tyFaceBdy c cube ie) \\ [fdir])
                      let (Ty _ specf) = tyFaceBdy c cube ie
                      return (ie, Fill fdir (Ty (tyDim cube - 2) (filter (\(je,t) -> je /= fdir) (sides ++ specf))))
                      ) fil
      return psol

-- Constraint management

singleConstraint :: Rs r w => Restr -> CVar -> [Term r w] -> Solving s () r w CVar
singleConstraint f cv hs = addConstraint cv $ do
  c <- gets ctxt
  ts <- lookupDom cv
  let ts' = catMaybes $ map (\t -> restrPTerm c t f hs) ts
  when (ts' /= ts) $ update cv ts'

boundaryConstraint :: Rs r w => Restr -> Restr -> Solving s () r w CVar
boundaryConstraint = addBinaryConstraint $ \cv dv -> do
  c <- gets ctxt
  let (cf , df) = adji cv dv

  ts <- lookupDom cv
  ss <- lookupDom dv
  let tsf = concatMap (\t -> ptermFace c t df) ts
  let ssg = concatMap (\t -> ptermFace c t cf) ss

  let hs = tsf `intersect` ssg

  guard (not (null hs))

  let ts' = catMaybes $ map (\t -> restrPTerm c t df hs) ts
  let ss' = catMaybes $ map (\t -> restrPTerm c t cf hs) ss

  when (ts' /= ts) $ update cv ts'
  when (ss' /= ss) $ update dv ss'


isVar :: Rs r w => (Restr,Restr) -> Solving s Bool r w FVar
isVar (ie,je) = do
  c <- gets ctxt
  cube <- gets goal
  return $ je `elem` unspec (tyFaceBdy c cube ie)


-- TODO UNFOLDING NECESSARY! OR MAKE CLEVERER INTERSECT
-- TODO GENERALISE TO NOT ONLY FVars, but also if one is already part of the cube
-- then this can be also used to setup initial domains
termsEqual :: Rs r w => (Restr,Restr) -> (Restr,Restr) -> Solving s () r w FVar
termsEqual = addBinaryConstraint $ \cv dv -> do
  c <- gets ctxt
  cube <- gets goal
  -- traceShowM $ "TERMS EQ OF " ++ show cv ++ " AND " ++ show dv
  ts <- ifM (isVar cv) (lookupDom cv) (return [get2Face c cube cv])
  ss <- ifM (isVar dv) (lookupDom dv) (return [get2Face c cube dv])
  let hs = ts `intersect` ss
  guard (not (null hs))
  whenM ((isVar cv) `andM` return (ts /= hs)) $ update cv hs
  whenM ((isVar dv) `andM` return (ss /= hs)) $ update dv hs


compsEqual :: Rs r w => (Restr,Restr) -> (Restr,Restr) -> Solving s () r w FVar
compsEqual (ie,fdir) (ie',fdir') = do
  -- traceShowM $ "COMPS EQ OF " ++ show (ie,fdir) ++ " AND " ++ show (ie',fdir')
  c <- gets ctxt
  cube <- gets goal
  let swap = if fdir == fdir'
        then id
        else (\j ->
           if j == fst fdir
             then fst fdir'
           else if j == fst fdir'
             then fst fdir
           else j
          )
  let swape = if snd fdir == snd fdir'
        then id
        else negI
  mapM_ (\(j,e) -> termsEqual (ie,(j,e)) (ie',(swap j,swape e)))
       (restrictions (tyDim cube-1) \\ [fdir])
  return ()


fboundaryConstraint :: Rs r w => FVar -> FVar -> Solving s () r w FVar
fboundaryConstraint = addBinaryConstraint $ \(ie,cv) (ie',dv) -> do
  -- traceShowM $ "BOUNDARIES EQ OF " ++ show (ie,cv) ++ " AND " ++ show (ie',dv)
  c <- gets ctxt
  let (cf , df) = adji cv dv

  ts <- lookupDom (ie,cv)
  ss <- lookupDom (ie',dv)
  let tsf = concatMap (\t -> ptermFace c t df) ts
  let ssg = concatMap (\t -> ptermFace c t cf) ss

  let hs = tsf `intersect` ssg

  guard (not (null hs))

  let ts' = catMaybes $ map (\t -> restrPTerm c t df hs) ts
  let ss' = catMaybes $ map (\t -> restrPTerm c t cf hs) ss

  -- guard (not (null ts'))
  -- guard (not (null ss'))

  when (ts' /= ts) $ update (ie,cv) ts'
  when (ss' /= ss) $ update (ie',dv) ss'






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
              -- , (2,I0) +> Var "p"
              , (2,I1) +> deg twop (Var "y") 1
                        ]

andGoal = Ty 2 [ (1,I0) +> deg twop (Var "x") 1
               , (1,I1) +> Var "p"
               , (2,I0) +> deg twop (Var "x") 1
               -- , (2,I1) +> Var "p"
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
                  , (2,I0) +> tinv threep (Var "q")
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
