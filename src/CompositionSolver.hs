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


data Solution = Pot PTerm | Fix Term
  deriving (Show, Eq)
type Domain = [Solution]

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
findComposition ctxt goal = listToMaybe (evalState compSolve (mkSEnv ctxt goal))


filterPSubsts :: [PTerm] -> [Restr] -> [Term] -> Solving s [PTerm]
filterPSubsts pts ies as = do
  ctxt <- gets ctxt
  catMaybes <$> mapM (\(PTerm p sigma) -> return (PTerm p <$> filterPSubst ctxt (PTerm p sigma) ies as)) pts


compSolve :: Solving s [Term]
compSolve = do
  goal <- gets goal
  traceM $ show goal
  ctxt <- gets ctxt
  traceM $ show (constr ctxt)

  let pterms = map (\f -> createPTerm f (dim goal)) (constr ctxt)

  let faceInd = [ (i,e) | i <- [1..dim goal], e <- [e0,e1]]-- getFaces (dim goal) (dim goal - 1)
  traceM $ show faceInd

  sides <- mapM (\(i,e) ->
          let a = boundaryFace goal (i,e) in
            case a of
              Term _ _ -> do
                ts <- filterPSubsts pterms [(dim goal-1,e1)] [a]
                newCVar (Side i e) (map Pot ts)
              Comp box -> newCVar (Side i e) [Fix (Filler box)]
            )
        faceInd
  back <- newCVar Back (map Pot pterms)

  domains <- mapM lookupDom (sides ++ [back])
  traceM $ "AFTER INIT\n" ++ concatMap ((++ "\n") . show) domains ++ "END"

  -- Impose back constraints
  mapM_ (\(i,e) -> boundaryConstraint [(dim goal-1,e0)] [(i,e)] (Side i e) Back) faceInd

  domains <- mapM lookupDom (sides ++ [back])
  traceM $ "AFTER BACK\n" ++ concatMap ((++ "\n") . show) domains ++ "END"

  mapM_ (\(i,e) -> mapM_ (\(i',e') ->
                            boundaryConstraint [(i,e')] [(i,e)] (Side i e) (Side i' e')
                            ) [ (i',e') | i' <- [i+1 .. dim goal-1] , e' <- [e0,e1]]) faceInd

  domains <- mapM lookupDom (sides ++ [back])
  traceM $ "AFTER SIDE\n" ++ concatMap ((++ "\n") . show) domains ++ "END"

  ress <- splitAltern <$> mapM firstSubst sides
  resb <- firstSubst back

  -- return []
  let sol = [Comp (Box (uncurry zip ress) resb)]
  traceM "SOLVED"
  (traceM . show) sol
  return sol



possibleTerms :: Solution -> [Restr] -> Solving s [Term]
possibleTerms (Pot ps) ies = do
  ctxt <- gets ctxt
  return $ map snd $ possibleFaces ctxt ps ies
possibleTerms (Fix t) ies = do
  ctxt <- gets ctxt
  return [termRestr ctxt t ies]


filterSolution :: Solution -> [Restr] -> [Term] -> Solving s (Maybe Solution)
filterSolution (Pot (PTerm p sigma)) ie hs = do
  ctxt <- gets ctxt
  return $ case filterPSubst ctxt (PTerm p sigma) ie hs of
          Just sigma' -> Just $ Pot (PTerm p sigma')
          Nothing -> Nothing
filterSolution (Fix t) ie hs = do
  ctxt <- gets ctxt
  return $ if termRestr ctxt t ie `elem` hs
          then Just $ Fix t
          else Nothing

boundaryConstraint :: [Restr] -> [Restr] -> CVar -> CVar -> Solving s ()
boundaryConstraint ie jf = addBinaryConstraint $ \c d -> do
  ctxt <- gets ctxt
  pss <- lookupDom c
  qss <- lookupDom d

  traceM $ "pss " ++ show (length pss) ++ show pss
  traceM $ "qss " ++ show (length qss) ++ show qss

  fs <- nub . concat <$> mapM (`possibleTerms` ie) pss
  gs <- nub . concat <$> mapM (`possibleTerms` jf) qss

  traceM $ "POSSIBLE fs: " ++ show fs
  traceM $ "POSSIBLE gs: " ++ show gs

  -- Take intersection
  let hs = fs `intersect` gs

  traceM $ "COMMON BOUNDARY: " ++ show hs

  pss' <- catMaybes <$> mapM (\ps -> filterSolution ps ie hs) pss
  qss' <- catMaybes <$> mapM (\qs -> filterSolution qs jf hs) qss

  traceM $ show pss'
  traceM $ show qss'
  when (null pss') $ traceM $ "EMPTY " ++ show c
  when (null qss') $ traceM $ "EMPTY " ++ show d
  -- guard $ not $ null pss'
  -- guard $ not $ null qss'
  when (pss' /= pss) $ update c pss'
  when (qss' /= qss) $ update d qss'



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
  --       \(PTerm f sigma) hs -> if null hs
  --                     then Nothing
  --                     else Just (PTerm f (updateGadgets sigma (map fst hs) ie))
  --       \()
  --       ) pss fs'
  -- let qs' = catMaybes $ zipWith (\(PTerm f sigma) hs -> if null hs
  --                     then Nothing
  --                     else Just (PTerm f (updateGadgets sigma (map fst hs) ie))) qss gs'

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
  vals <- lookupDom var
  case head vals of
    Pot (PTerm f sigma) -> do
      let newval = PTerm f (injPSubst (fstSubst sigma))
      when ([Pot newval] /= vals) $ update var [Pot newval]
      return (pterm2term newval)
    Fix t -> return t


-- TODO IMPLEMENT GUARD


-- equalVertex :: Vert -> Vert -> CVar -> CVar -> Solving s ()
-- equalVertex v u = addBinaryConstraint $ \x y -> do
--   xs <- lookupDom x
--   ys <- lookupDom y

--   -- Find all the points that v could be with the partial substitutions in the domain
--   pxv <- nub . concat <$> mapM (\(PTerm f s) -> mapM (evalPoint f) (s ! v)) xs
--   pyu <- nub . concat <$> mapM (\(PTerm f s) -> mapM (evalPoint f) (s ! u)) ys
--   let ps = intersect pxv pyu

--   xs' <- filterPSubsts v ps xs
--   ys' <- filterPSubsts u ps ys
--   guard $ not $ null xs'
--   guard $ not $ null ys'
--   when (xs' /= xs) $ update x xs'
--   when (ys' /= ys) $ update y ys'

-- equalVertices :: CVar -> CVar -> [(Vert , Vert)] -> Solving s ()
-- equalVertices x y vus = mapM (\(v,u) -> equalVertex v u x y) vus >> return ()




-- -- Edge constraints

-- getEdges :: PTerm -> IVar -> Endpoint -> Solving s [Term]
-- getEdges ps i e = do
--   -- trace $ show ps ++ " | " ++ show i ++ "@" ++ show e
--   let PTerm f sigma = ps
--   let vs = sigma ! Vert (map (\j -> if i /= j then e else e0) [1..2])
--   let us = sigma ! Vert (map (\j -> if i /= j then e else e1) [1..2])
--   -- trace $ show vs ++ " --> " ++ show us

--   mapM (\v -> mapM (evalEdge f v) (filter (`below` v) us)) vs >>= return . catMaybes . concat


-- -- TODO COMPUTE BOUNDARY ONLY ONCE BY KEEPING TRACK OF WHICH ASSIGNMENTS GAVE RISE TO CERTAIN BOUNDARY
-- checkPTermEdge :: IVar -> Endpoint -> [Term] -> PTerm -> Solving s (Maybe PTerm)
-- checkPTermEdge i e fs (PTerm f sigma) = do
--   fdim <- dimTerm f
--   case fdim of
--     0 -> if (emptT f `elem` fs) then return $ Just (PTerm f sigma) else return Nothing
--     _ -> do
--       -- trace $ show "Restrict " ++ show (f , sigma) ++ "|" ++ show i ++ "@" ++ show e ++ " to boundaries " ++ show fs

--       let x = Vert (map (\j -> if i /= j then e else e0) [1..2])
--       let y = Vert (map (\j -> if i /= j then e else e1) [1..2])

--       let vs = sigma ! x
--       let us = sigma ! y

--       vs' <- filterM (\v -> anyM (\u -> evalEdge f v u >>= \g ->
--                                      case g of
--                                        Just g' -> return (g' `elem` fs)
--                                        Nothing -> return False
--                                      ) us) vs
--       us' <- filterM (\u -> anyM (\v -> evalEdge f v u >>= \g ->
--                                      case g of
--                                        Just g' -> return (g' `elem` fs)
--                                        Nothing -> return False
--                                      ) vs') us
--       if null vs' || null us'
--         then return Nothing
--         else do
--           let sigma' = Map.insert x vs' sigma
--           let sigma'' = Map.insert x vs' sigma'
--           let propagate = Map.mapWithKey (\z ws -> filter (\w ->
--                                                             (z `above` x) --> any (w `above`) vs' &&
--                                                             (z `below` x) --> any (w `below`) vs' &&
--                                                             (z `above` y) --> any (w `above`) us' &&
--                                                             (z `below` y) --> any (w `below`) us'
--                                                           ) ws) sigma''
--           return $ Just (PTerm f propagate)





-- filterPSubstsEdge :: IVar -> Endpoint -> [Term] -> [PTerm] -> Solving s [PTerm]
-- filterPSubstsEdge i e fs ss = mapM (checkPTermEdge i e fs) ss >>= return . catMaybes

-- equalEdge :: IVar -> Endpoint -> IVar -> Endpoint -> CVar -> CVar -> Solving s ()
-- equalEdge i e j e' = addBinaryConstraint $ \x y -> do
--   xs <- lookupDom x
--   ys <- lookupDom y

--   exs <- mapM (\sigma -> getEdges sigma i e) xs >>= return . nub . concat
--   eys <- mapM (\sigma -> getEdges sigma j e') ys >>= return . nub . concat

--   -- TODO rename to fs to avoid clash with endpoint lists es
--   let es = intersect exs eys

--   xs' <- filterPSubstsEdge i e es xs
--   ys' <- filterPSubstsEdge j e' es ys
--   guard $ not $ null xs'
--   guard $ not $ null ys'
--   when (xs' /= xs) $ update x xs'
--   when (ys' /= ys) $ update y ys'



-- What to do with degeneracies equivalent to a face? e.g.
-- "seg" fromList [(0,[0]),(1,[0])]
-- is the same as its left face


-- evalFace :: Term -> Vert -> Solving s Term
-- evalFace (Term f s) x = do
--   goal <- gets goal
--   let sigma = tele2Subst s (dim goal - 1)
--   trace $ show sigma

--   return $ emptT "asd"

-- evalBoundary :: Boundary -> Vert -> Solving s Term
-- evalBoundary (Boundary ((a , b) : _)) (Vert (Endpoint e : es)) =
--   evalFace (if e then b else a) (Vert es)

-- evalBoundary (Boundary [(Term a _ , Term b _)]) (Vert [Endpoint e]) = return $ Point (if e then b else a)
-- evalBoundary (Boundary [(Term a _ , Term b _) , _]) (Vert [Endpoint e , Endpoint e']) =
--   evalPoint (if e then b else a) (Vert [Endpoint e'])
-- evalBoundary (Boundary [(Term a _ , Term b _) , _ , _]) (Vert (Endpoint e : es)) =
--   evalPoint (if e then b else a) (Vert es)


-- evalBoundary1 :: Boundary -> [Vert] -> Solving s Term
-- -- evalBoundary1 (Boundary [(Term a _ , Term b _)]) (Vert [Endpoint e]) (Vert [Endpoint e]) = return $ Point (if e then b else a)
-- evalBoundary1 (Boundary fs) [x , y] = do
--   let (i , Endpoint e) = getBoundary x y
--   trace $ show i ++ "|" ++ show e
--   let res = (if e then snd else fst) (fs !! (i - 1))
--   trace $ show res
--   return res

-- filterPTerm1 :: [Vert] -> [Term] -> PTerm -> Solving s (Maybe PTerm)
-- filterPTerm1 [x , y] fs (PTerm f sigma) = do
--   fdim <- dimTerm f
--   case fdim of
--     0 -> if (emptT f `elem` fs) then return $ Just (PTerm f sigma) else return Nothing
--     _ -> do
--       let vs = sigma ! x
--       let us = sigma ! y

--       vs' <- filterM (\v -> anyM (\u -> evalEdge f v u >>= \g ->
--                                      case g of
--                                        Just g' -> return (g' `elem` fs)
--                                        Nothing -> return False
--                                      ) us) vs
--       us' <- filterM (\u -> anyM (\v -> evalEdge f v u >>= \g ->
--                                      case g of
--                                        Just g' -> return (g' `elem` fs)
--                                        Nothing -> return False
--                                      ) vs') us
--       if null vs' || null us'
--         then return Nothing
--         else do
--           let sigma' = Map.insert x vs' sigma
--           let sigma'' = Map.insert x vs' sigma'
--           let propagate = Map.mapWithKey (\z ws -> filter (\w ->
--                                                             (z `above` x) --> any (w `above`) vs' &&
--                                                             (z `below` x) --> any (w `below`) vs' &&
--                                                             (z `above` y) --> any (w `above`) us' &&
--                                                             (z `below` y) --> any (w `below`) us'
--                                                           ) ws) sigma''
--           return $ Just (PTerm f propagate)
