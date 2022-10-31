{-# LANGUAGE FlexibleContexts #-}

module Solver where

import Data.List
import Data.Maybe
import Control.Monad.Except
import Control.Monad.State
import qualified Data.Set as Set
import Data.Map.Strict (Map, (!), restrictKeys)
import qualified Data.Map.Strict as Map

import Prel
import Data
import Poset


-- Constraint variables are just indices
type CVar = Int

-- The Solving monad
type Solving s a = StateT (SEnv s) (ExceptT String IO) a

-- For each constraint variable we save the constraints that still need to be checked as well as the current domain
data CVarInfo a = CVarInfo { delayedConstraints :: Solving a (), values :: [PTerm] }

data SEnv s =
  SEnv { cube :: Cube
       , goal :: Boundary
       , varSupply :: Int
       , varMap :: Map Int (CVarInfo s)
       , verbose :: Bool
       }

mkSEnv :: Cube -> Boundary -> Bool -> SEnv s
mkSEnv c g = SEnv c g 0 Map.empty

trace :: String -> Solving s ()
trace s = do
  b <- gets verbose
  when b $ liftIO (putStrLn s)

-- lookupDef :: Id -> Solving s Boundary
-- lookupDef name = do
--   c <- gets cube
--   case lookup name (map decl2pair (constr c)) of
--     Just face -> return face
--     Nothing -> throwError $ "Could not find definition of " ++ name




-- -- COMPUTE AND RESTRICT BOUNDARIES

-- -- Given a face and a selection of vertices, compute its face
-- -- E.g., for p : x -> y we have
-- --          evalFace p [0,1] = p [0->0, 1->1]
-- --          evalFace p [0,0] = x [0->, 1->]
-- evalFace :: Id -> [Vert] -> Solving s Term
-- evalFace f vs = do
--   ty <- lookupDef f
--   case dim ty of
--     0 -> return $ Term f (constSubst (log2 (length vs)))
--     n -> if any (\u -> head vs `vdiff` u > n-1) (tail vs)
--         then return $ Term f (reconstrPMap vs)
--         else evalBoundary ty vs

-- -- Given a selection of vertices xs, select the part of the boundary
-- -- prescribed by xs
-- evalBoundary :: Boundary -> [Vert] -> Solving s Term
-- evalBoundary (Boundary fgs) xs = do
--   let (i , Endpoint e) = getFirstCommon xs
--   let (a , b) = fgs !! (i - 1)
--   let (Term f subst) = if e then b else a
--   evalFace f (map (\x -> subst ! removeInd x i) xs)







-- -- Restrict a potential substitution such that the face prescribed by xs is in as
-- checkPTerm :: [Vert] -> [Term] -> PTerm -> Solving s (Maybe PTerm)
-- checkPTerm xs as (PTerm f sigma) = do
--   -- Compute all the ways in which we could build a face from the values in the
--   -- potential substitution
--   let gadgets = map (map snd . Map.toList) (getSubsts (sigma `restrictKeys` Set.fromList xs))

--   -- evaluate f at each of these faces and retain only those gadgets which yield
--   -- a face which is in as
--   gadgets' <- filterM (evalFace f >=> \b -> return (b `elem` as)) gadgets

--   -- Combine result by forgetting about which vertices led to which face, we
--   -- only keep track of whether there is some vertex for which a face could
--   -- be found which is in as
--   let vus = map (\i -> nub (map (!!i) gadgets')) [0 .. length xs - 1]

--   -- If there is some empty domain for a vertex, the potential substitution is
--   -- not a valid substitution and we return nothing. Otherwise we update the
--   -- poset map
--   return $ if any null vus
--     then Nothing
--     else Just $ PTerm f $ foldl (\s (x , vu) -> updatePSubst s x vu) sigma (zip xs vus)
--   -- TODO ALSO CHECK IN updatePSubst WHETHER SOME VALUATIONS TURN EMPTY?


-- filterPSubsts :: [Vert] -> [Term] -> [PTerm] -> Solving s [PTerm]
-- filterPSubsts xs as pts = catMaybes <$> mapM (checkPTerm xs as) pts


-- boundaryConstraint :: [Vert] -> [Vert] -> CVar -> CVar -> Solving s ()
-- boundaryConstraint xs ys = addBinaryConstraint $ \c d -> do
--   -- trace $ show c ++ "|" ++ show xs ++ " vs " ++ show d ++ "|" ++ show ys

--   ps <- lookupDom c
--   qs <- lookupDom d

--   fs <- mapM (\(PTerm f sigma) -> mapM (\gad -> do
--                                            let vs = (map snd . Map.toList) gad
--                                            a <- evalFace f vs
--                                            return (f , gad , a)
--                                        ) (getSubsts (sigma `restrictKeys` Set.fromList xs))
--              ) ps
--   gs <- mapM (\(PTerm f sigma) -> mapM (\gad -> do
--                                            let vs = (map snd . Map.toList) gad
--                                            a <- evalFace f vs
--                                            return (f , gad , a)
--                                        ) (getSubsts (sigma `restrictKeys` Set.fromList ys))
--              ) qs

--   -- trace "POSSIBLE fs"
--   -- trace $ show fs
--   -- trace "POSSIBLE gs"
--   -- trace $ show gs

--   -- Take intersection
--   let fs' = map (filter (\(_ , _ , t) -> any (\(_ , _ , s) -> s == t) (concat gs))) fs
--   let gs' = map (filter (\(_ , _ , t) -> any (\(_ , _ , s) -> s == t) (concat fs))) gs

--   -- trace "NEW fs"
--   -- trace $ show fs'
--   -- trace "NEW gs"
--   -- trace $ show gs'

--   -- Combine all results
--   let ps' = catMaybes $ zipWith (\(PTerm f sigma) hs -> if null hs
--                       then Nothing
--                       else Just $ PTerm f (foldl (\s x -> updatePSubst s x (nub (map (\(_,gad,_) -> gad ! x) hs))) sigma xs))
--             ps fs'
--   let qs' = catMaybes $ zipWith (\(PTerm f sigma) hs -> if null hs
--                       then Nothing
--                       else Just $ PTerm f (foldl (\s x -> updatePSubst s x (nub (map (\(_,gad,_) -> gad ! x) hs))) sigma ys))
--             qs gs'

--   -- TODO UPDATE POSET MAPS!!!

--   -- trace $ show ps
--   -- trace $ show ps'
--   -- trace $ show qs
--   -- trace $ show qs'
--   -- when (null ps') $ trace $ "EMPTY " ++ show c
--   -- when (null qs') $ trace $ "EMPTY " ++ show d
--   guard $ not $ null ps'
--   guard $ not $ null qs'
--   when (ps' /= ps) $ update c ps'
--   when (qs' /= qs) $ update d qs'

-- -- equalVertex :: Vert -> Vert -> CVar -> CVar -> Solving s ()
-- -- equalVertex v u = addBinaryConstraint $ \x y -> do
-- --   xs <- lookupDom x
-- --   ys <- lookupDom y

-- --   -- Find all the points that v could be with the partial substitutions in the domain
-- --   pxv <- nub . concat <$> mapM (\(PTerm f s) -> mapM (evalPoint f) (s ! v)) xs
-- --   pyu <- nub . concat <$> mapM (\(PTerm f s) -> mapM (evalPoint f) (s ! u)) ys
-- --   let ps = intersect pxv pyu

-- --   xs' <- filterPSubsts v ps xs
-- --   ys' <- filterPSubsts u ps ys
-- --   guard $ not $ null xs'
-- --   guard $ not $ null ys'
-- --   when (xs' /= xs) $ update x xs'
-- --   when (ys' /= ys) $ update y ys'





-- -- DOMAIN AND CONSTRAINT MANAGEMENT

-- newCVar :: [PTerm] -> Solving s Int
-- newCVar domain = do
--     v <- nextCVar
--     v `isOneOf` domain
--     return v
--     where
--         nextCVar = do
--             s <- get
--             let v = varSupply s
--             put $ s { varSupply = v + 1 }
--             return v
--         x `isOneOf` domain =
--             modify $ \s ->
--                 let vm = varMap s
--                     vi = CVarInfo {
--                         delayedConstraints = return (),
--                         values = domain}
--                 in
--                 s { varMap = Map.insert x vi vm }

-- emptyConstraints :: Solving s ()
-- emptyConstraints = do
--   s <- get
--   put $ s { varMap = Map.map (\vi -> CVarInfo { values = values vi , delayedConstraints = return() }) (varMap s) }


-- lookupDom :: Int -> Solving s [PTerm]
-- lookupDom x = do
--     s <- get
--     return . values $ varMap s ! x

-- update :: Int -> [PTerm] -> Solving s ()
-- update x i = do
--     s <- get
--     let vm = varMap s
--     let vi = vm ! x
--     put $ s { varMap = Map.insert x (vi { values = i }) vm }
--     delayedConstraints vi


-- addConstraint :: Int -> Solving s () -> Solving s ()
-- addConstraint x constraint = do
--     s <- get
--     let vm = varMap s
--     let vi = vm ! x
--     let cs = delayedConstraints vi
--     put $ s { varMap =
--         Map.insert x (vi { delayedConstraints = cs >> constraint }) vm }

-- type BinaryConstraint s = Int -> Int -> Solving s ()
-- addBinaryConstraint :: BinaryConstraint s -> BinaryConstraint s
-- addBinaryConstraint f x y = do
--     let constraint  = f x y
--     constraint
--     addConstraint x constraint
--     addConstraint y constraint




-- -- Commit to the first substitution of a given constraint variable
-- firstSubst :: CVar -> Solving s PTerm
-- firstSubst var = do
--   vals <- lookupDom var
--   let PTerm f sigma = head vals
--   let newval = PTerm f (injPSubst (fstSubst sigma))
--   when ([newval] /= vals) $ update var [newval]
--   return newval




