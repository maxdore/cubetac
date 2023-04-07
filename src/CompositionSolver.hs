{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}

module CompositionSolver where

import Control.Monad
import Control.Monad.State
import Data.Ord
import Data.Maybe
import Data.List
import qualified Data.Map as Map
import Data.Map ((!), Map)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Either

import Prel
import Data
import Poset
import Formula
import ContortionSolver

import Debug.Trace
-- traceM :: Applicative f => String -> f ()
-- traceM _ = pure ()


type CVar = BoxFace

-- The Solving monad
type Solving s a = StateT (SEnv s) [] a
-- newtype Solving s a = Solving { unSolving :: StateT (SEnv s) [] a }
--     deriving (Monad)
    -- deriving (Monad, MonadPlus, MonadState (SEnv s))

-- A constraint variable can either be a collection of potential contortion,
-- fixed to a certain term, or be left open
data Domain = Pot [PContortion] | Fix Term | Open
  deriving (Show, Eq)

-- For each constraint variable we save the constraints that still need to be
-- checked as well as the current domain
data CVarInfo a = CVarInfo { delayedConstraints :: Solving a (), values :: Domain }


data SEnv s =
  SEnv { ctxt :: Cube
       , goal :: Boundary
       , fixed :: [CVar]
       , open :: [CVar]
       , varMap :: Map CVar (CVarInfo s)
       }


lookupDef :: Id -> Solving s Boundary
lookupDef name = do
  c <- gets ctxt
  case lookup name (map decl2pair (constr c)) of
    Just face -> return face
    Nothing -> error $ "Could not find definition of " ++ name


incps :: [a] -> [[a]]
incps = (sortBy (comparing (length))) . (filterM (const [True, False]))


findComposition :: Cube -> Boundary -> Maybe Term
findComposition ctxt goal =
  let fixed = map Side (getCompFaces goal) in -- TODO
  let nocont = [] in -- TODO
  let free = map Side (getFreeFaces goal) in
  let couldbe = Back : (((map Side (restrictions (dim goal)) \\ fixed) \\ nocont) \\ free) in
  case (catMaybes $
        (map (\uns -> run fixed (nocont ++ uns)) (incps free))
        ++ (map (\uns -> run fixed (nocont ++ free ++ uns)) (tail (incps couldbe)))
       ) of
    ((Comp t):_) -> Just $ Comp (insertFillers ctxt goal t)
    [] -> Nothing

    where
      run :: [CVar] -> [CVar] -> Maybe Term
      run fixed open = listToMaybe $ evalStateT (runCS) (SEnv ctxt goal fixed open Map.empty)


-- OR return that face is extra?
insertFillers :: Cube -> Boundary -> Box -> Box
insertFillers ctxt goal res@(Box ress resb) =
        modifyBox res (\(i,e) t ->
          if boundaryFace goal (i,e) == Free && t == Free
            then Fill (Box
                        (map (\j -> let ss = ress!!(j-1) in
                                (termRestr ctxt (fst ss) [(i-1,e)] , termRestr ctxt (snd ss) [(i-1,e)])) [ j | j <- [1..dim goal], j /= i])
                        (termFace ctxt resb (i,e)))
            else t
          ) id

runCS :: Solving s Term
runCS = do
  goal <- gets goal
  ctxt <- gets ctxt
  fixed <- gets fixed
  open <- gets open

  traceM $ "RUNNING CSP WITH OPEN SIDES " ++ show open

  let pterms = map (\f -> createPContortion f (dim goal)) (constr ctxt)
  let faceInd = restrictions (dim goal)

  sides <- mapM (\ie ->
                   if Side ie `elem` open
                     then newCVar (Side ie) Open
                     else
                      let f = boundaryFace goal ie in
                        case f of
                          Term _ _ -> do
                            ts <- filterPSubsts pterms [(dim goal,e1)] [f]
                            v <- newCVar (Side ie) (Pot ts)
                            singleConstraint [(dim goal,e1)] (Side ie) [f]
                            return v

                          -- TODO insert fills more subtly -- sometimes not possible to unfold all comps
                          Comp box -> newCVar (Side ie) (Fix (Fill box))
                          Free -> newCVar (Side ie) (Pot pterms)
            )
        faceInd
  back <- newCVar Back (if Back `elem` open then Open else (Pot pterms))

  -- domains <- mapM lookupDom (sides ++ [back])
  -- traceM $ "AFTER INIT\n" ++ concatMap ((++ "\n") . show) domains ++ "END"

  -- Impose side constraints
  -- mapM_ (\(i,e) -> mapM_ (\(i',e') ->
  --                           boundaryConstraint [(i,e')] [(i,e)] (Side i e) (Side i' e')
  --                           ) [ (i',e') | i' <- [i+1 .. dim goal] , e' <- [e0,e1]]) faceInd
  mapM_ (\(i,e) -> mapM_ (\(j,f) ->
                            boundaryConstraint [(j-1,f)] [(i,e)] (Side (i,e)) (Side (j,f))
                            ) [ (j,f) | j <- [i+1 .. dim goal] , f <- [e0,e1]]) faceInd

  -- domains <- mapM lookupDom (sides ++ [back])
  -- traceM $ "AFTER SIDE\n" ++ concatMap ((++ "\n") . show) domains ++ "END"

  -- Impose back constraints
  mapM_ (\ie -> boundaryConstraint [(dim goal,e0)] [ie] (Side ie) Back) faceInd

  -- domains <- mapM lookupDom (sides ++ [back])
  -- traceM $ "AFTER BACK\n" ++ concatMap ((++ "\n") . show) domains ++ "END"

  -- mapM_ (\ie -> singleConstraint [(dim goal,e0)] (Side ie) [boundaryFace goal ie]) faceInd

  ress <- uncurry zip <$> (splitAltern <$> mapM getSol sides)
  resb <- getSol back
  return $ Comp (Box ress resb)


possibleTerms :: Domain -> [Restr] -> Solving s [Term]
possibleTerms (Pot ps) ies = do
  ctxt <- gets ctxt
  return $ (nub . concat) (map (\p -> map snd (possibleFaces ctxt p ies)) ps )
possibleTerms (Fix t) ies = do
  ctxt <- gets ctxt
  return [termRestr ctxt t ies]

filterPSubsts :: [PContortion] -> [Restr] -> [Term] -> Solving s [PContortion]
filterPSubsts pts ies as = do
  ctxt <- gets ctxt
  catMaybes <$> mapM (\(PContortion p sigma) ->
                        return (filterPSubst ctxt (PContortion p sigma) ies as))
                     pts

filterSolution :: Domain -> [Restr] -> [Term] -> Solving s Domain
filterSolution (Pot ps) ie hs = do
  ctxt <- gets ctxt
  let ps' = catMaybes $ map (\p -> filterPSubst ctxt p ie hs) ps
  guard (not (null ps'))
  return $ Pot ps'
filterSolution (Fix t) ie hs = do
  ctxt <- gets ctxt
  guard (termRestr ctxt t ie `elem` hs)
  return $ Fix t

singleConstraint :: [Restr] -> CVar -> [Term] -> Solving s ()
singleConstraint ie c hs = addConstraint c $ do
  pss <- lookupDom c
  -- traceM $ show (pss) ++ "@" ++ show ie ++ " constrained to " ++ show hs
  when (pss /= Open) $ do
    fs <- possibleTerms pss ie
    pss' <- filterSolution pss ie (fs `intersect` hs)
    when (pss' /= pss) $ update c pss'

boundaryConstraint :: [Restr] -> [Restr] -> CVar -> CVar -> Solving s ()
boundaryConstraint ie jf = addBinaryConstraint $ \c d -> do
  pss <- lookupDom c
  qss <- lookupDom d

  when (pss /= Open && qss /= Open) $ do
    fs <- possibleTerms pss ie
    gs <- possibleTerms qss jf

    let hs = fs `intersect` gs

    pss' <- filterSolution pss ie hs
    qss' <- filterSolution qss jf hs

    when (pss' /= pss) $ update c pss'
    when (qss' /= qss) $ update d qss'


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

-- emptyConstraints :: Solving s ()
-- emptyConstraints = do
--   s <- get
--   put $ s { varMap = Map.map (\vi -> CVarInfo { values = values vi , delayedConstraints = return() }) (varMap s) }

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
    Pot ((PContortion f sigma) : _) -> do
      sol <- lift (map (Term f) (getSubsts sigma))
      update var (Fix sol)
      return sol
    Fix t -> return t
    Open -> return Free

