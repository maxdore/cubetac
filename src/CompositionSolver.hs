{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Strict #-}

module CompositionSolver where

import Control.Monad
import Control.Monad.State
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

-- Constraint variables are just indices
data CVar = Back | Side IVar Endpoint
  deriving (Show, Eq , Ord)

-- The Solving monad
type Solving s a = State (SEnv s) a


data Domain = Pot [PContortion] | Fix Term | Open
  deriving (Show, Eq)

-- For each constraint variable we save the constraints that still need to be checked as well as the current domain
data CVarInfo a = CVarInfo { delayedConstraints :: Solving a (), values :: Domain }


data SEnv s =
  SEnv { ctxt :: Cube
       , goal :: Boundary
       , varSupply :: Int
       , varMap :: Map CVar (CVarInfo s)
       }

mkSEnv :: Cube -> Boundary -> SEnv s
mkSEnv c g = SEnv c g 0 Map.empty


lookupDef :: Id -> Solving s Boundary
lookupDef name = do
  c <- gets ctxt
  case lookup name (map decl2pair (constr c)) of
    Just face -> return face
    Nothing -> error $ "Could not find definition of " ++ name


findComposition :: Cube -> Boundary -> Maybe Term
findComposition ctxt goal = evalState compSolve (mkSEnv ctxt goal)


filterPSubsts :: [PContortion] -> [Restr] -> [Term] -> Solving s [PContortion]
filterPSubsts pts ies as = do
  ctxt <- gets ctxt
  catMaybes <$> mapM (\(PContortion p sigma) -> return (filterPSubst ctxt (PContortion p sigma) ies as)) pts


compSolve :: Solving s (Maybe Term)
compSolve = do
  goal <- gets goal
  -- traceM $ show goal
  ctxt <- gets ctxt

  let pterms = map (\f -> createPContortion f (dim goal)) (constr ctxt)

  let faceInd = [ (i,e) | i <- [1..dim goal], e <- [e0,e1]]

  sides <- mapM (\(i,e) ->
          let a = boundaryFace goal (i,e) in
            -- traceShow a $
            case a of
              Term _ _ -> do
                ts <- filterPSubsts pterms [(dim goal,e1)] [a]
                newCVar (Side i e) (Pot ts)
              -- TODO fill more cleverly -- sometimes not possible to unfold all comps
              Comp box -> newCVar (Side i e) (Fix (Fill box))
              Free -> newCVar (Side i e) Open
            )
        faceInd
  back <- newCVar Back (Pot pterms)

  -- TODO UPDATE WHICH FACES WE WON'T BE ABLE TO FILL?
  -- go through all sides and check if after unfolding hcomps (and given goal boundary)
  -- we know that some face cannot be filled with a contortion

  -- domains <- mapM lookupDom (sides ++ [back])
  -- traceM $ "AFTER INIT\n" ++ concatMap ((++ "\n") . show) domains ++ "END"

  -- Impose side constraints
  mapM_ (\(i,e) -> mapM_ (\(i',e') ->
                            boundaryConstraint [(i,e')] [(i,e)] (Side i e) (Side i' e')
                            ) [ (i',e') | i' <- [i+1 .. dim goal] , e' <- [e0,e1]]) faceInd

  -- domains <- mapM lookupDom (sides ++ [back])
  -- traceM $ "AFTER SIDE\n" ++ concatMap ((++ "\n") . show) domains ++ "END"


  -- Impose back constraints
  mapM_ (\(i,e) -> boundaryConstraint [(dim goal,e0)] [(i,e)] (Side i e) Back) faceInd

  -- domains <- mapM lookupDom (sides ++ [back])
  -- traceM $ "AFTER BACK\n" ++ concatMap ((++ "\n") . show) domains ++ "END"


  ress <- (splitAltern <$> mapM firstSubst sides) >>= \asd -> return $ uncurry zip asd
  -- traceShowM ress
  resb <- firstSubst back
  let res = Box ress resb

  -- TODO check whether enough has been filled to just fill the rest with comps
  let withcomps =
        Comp $ modifyBox res (\(i,e) t ->
          if boundaryFace goal (i,e) == Free
            then Fill (Box
                        (map (\j -> let ss = ress!!(j-1) in
                                (termRestr ctxt (fst ss) [(i-1,e)] , termRestr ctxt (snd ss) [(i-1,e)])) [ j | j <- [1..dim goal], j /= i])
                        (termFace ctxt resb (i,e)))
            else t
          ) id
  return $ Just withcomps



possibleTerms :: Domain -> [Restr] -> Solving s [Term]
possibleTerms (Pot ps) ies = do
  ctxt <- gets ctxt
  return $ (nub . concat) (map (\p -> map snd (possibleFaces ctxt p ies)) ps )
possibleTerms (Fix t) ies = do
  ctxt <- gets ctxt
  return [termRestr ctxt t ies]


filterSolution :: Domain -> [Restr] -> [Term] -> Solving s Domain
filterSolution (Pot ps) ie hs = do
  ctxt <- gets ctxt
  let ps' = catMaybes $ map (\p -> filterPSubst ctxt p ie hs) ps
  return $ if null ps'
              then Open
              else Pot ps'

  -- traceM $ show pss'
  -- traceM $ show qss'
  -- when (null pss') $ traceM $ "EMPTY " ++ show c
  -- when (null qss') $ traceM $ "EMPTY " ++ show d
  -- guard $ not $ null pss'
  -- guard $ not $ null qss'

filterSolution (Fix t) ie hs = return $ Fix t
-- filterSolution (Fix t) ie hs = do
--   ctxt <- gets ctxt
--   return $ if termRestr ctxt t ie `elem` hs
--           then Fix t
--           else error "AIII"

boundaryConstraint :: [Restr] -> [Restr] -> CVar -> CVar -> Solving s ()
boundaryConstraint ie jf = addBinaryConstraint $ \c d -> do
  ctxt <- gets ctxt
  pss <- lookupDom c
  qss <- lookupDom d
  if pss /= Open && qss /= Open
    then do
      fs <- possibleTerms pss ie
      gs <- possibleTerms qss jf

      let hs = fs `intersect` gs

      pss' <- filterSolution pss ie hs
      qss' <- filterSolution qss jf hs

      when (pss' /= pss) $ update c pss'
      when (qss' /= qss) $ update d qss'
    else return ()



-- OLD TRY, only unfold once..
-- possibleTerms :: Solution -> [Restr] -> Solving s (Either Term [(Subst , Term)])
-- possibleTerms (Pot ps) ies = do
--   ctxt <- gets ctxt
--   return $ Right $ possibleFaces ctxt ps ies
-- possibleTerms (Fix t) ies = do
--   ctxt <- gets ctxt
--   return $ Left $ termRestr ctxt t ies

-- getPossibleTerms :: Either Term [(Subst , Term)] -> [Term]
-- getPossibleTerms (Left t) = [t]
-- getPossibleTerms (Right sts) = map snd sts

-- filterPossibleTerms :: Either Term [(Subst , Term)] -> [Term] -> Bool
-- filterPossibleTerms (Left t) qs = t `elem` qs

-- boundaryConstraint :: [Restr] -> [Restr] -> CVar -> CVar -> Solving s ()
-- boundaryConstraint ie jf = addBinaryConstraint $ \c d -> do
--   ctxt <- gets ctxt
--   pss <- lookupDom c
--   qss <- lookupDom d

--   traceM $ "pss " ++ show (length pss) ++ show pss
--   traceM $ "qss " ++ show (length qss) ++ show qss

--   fs <- mapM (`possibleTerms` ie) pss
--   gs <- mapM (`possibleTerms` jf) qss

--   traceM $ "POSSIBLE fs: " ++ show (zip pss fs)
--   traceM $ "POSSIBLE gs: " ++ show (zip qss gs)

--   -- -- -- Take intersection
--   let fs' = map (\eth -> filter (\(_ , t) -> any (\(_ , s) -> s == t) (concat (map getPossibleTerms gs)))) fs
--   -- let gs' = map (filter (\(_ , t) -> any (\(_ , s) -> s == t) (concat fs))) gs

  -- traceM $ "NEW fs: " ++ show (zip pss fs')
  -- traceM $ "NEW gs: " ++ show (zip qss gs')


--   -- Combine all results
  -- let ps' = catMaybes $ zipWith (
  --       \(PContortion f sigma) hs -> if null hs
  --                     then Nothing
  --                     else Just (PContortion f (updateGadgets sigma (map fst hs) ie))
  --       \()
  --       ) pss fs'
  -- let qs' = catMaybes $ zipWith (\(PContortion f sigma) hs -> if null hs
  --                     then Nothing
  --                     else Just (PContortion f (updateGadgets sigma (map fst hs) ie))) qss gs'

  -- TODO UPDATE POSET MAPS!!! -- WHAT DID I MEAN BY THIS?

  -- traceM $ show pss
  -- traceM $ show ps'
  -- traceM $ show qss
  -- traceM $ show qs'
  -- when (null ps') $ traceM $ "EMPTY " ++ show c
  -- when (null qs') $ traceM $ "EMPTY " ++ show d
  -- -- guard $ not $ null ps'
  -- -- guard $ not $ null qs'
  -- when (ps' /= pss) $ update c ps'
  -- when (qs' /= qss) $ update d qs'

  return ()





-- -- DOMAIN AND CONSTRAINT MANAGEMENT

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




-- Commit to the first substitution of a given constraint variable
firstSubst :: CVar -> Solving s Term
firstSubst var = do
  val <- lookupDom var
  case val of
    Pot ((PContortion f sigma) : _) -> do
      let sol = Term f (fstSubst sigma)
      update var (Fix sol)
      return sol
    Fix t -> return t
    Open -> return Free


-- TODO IMPLEMENT GUARD


