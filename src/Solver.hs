{-# LANGUAGE FlexibleContexts #-}

module Solver where

import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map as Map
import Data.Map ((!), Map)


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

lookupDef :: Id -> Solving s Boundary
lookupDef name = do
  c <- gets cube
  case lookup name (map decl2pair (constr c)) of
    Just face -> return face
    Nothing -> throwError $ "Could not find definition of " ++ name


-- DOMAIN AND CONSTRAINT MANAGEMENT

newCVar :: [PTerm] -> Solving s Int
newCVar domain = do
    v <- nextCVar
    v `isOneOf` domain
    return v
    where
        nextCVar = do
            s <- get
            let v = varSupply s
            put $ s { varSupply = (v + 1) }
            return v
        x `isOneOf` domain =
            modify $ \s ->
                let vm = varMap s
                    vi = CVarInfo {
                        delayedConstraints = return (),
                        values = domain}
                in
                s { varMap = Map.insert x vi vm }

emptyConstraints :: Solving s ()
emptyConstraints = do
  s <- get
  put $ s { varMap = Map.map (\vi -> CVarInfo { values = values vi , delayedConstraints = return() }) (varMap s) }


lookupDom :: Int -> Solving s [PTerm]
lookupDom x = do
    s <- get
    return . values $ varMap s ! x

update :: Int -> [PTerm] -> Solving s ()
update x i = do
    s <- get
    let vm = varMap s
    let vi = vm ! x
    put $ s { varMap = Map.insert x (vi { values = i }) vm }
    delayedConstraints vi


addConstraint :: Int -> Solving s () -> Solving s ()
addConstraint x constraint = do
    s <- get
    let vm = varMap s
    let vi = vm ! x
    let cs = delayedConstraints vi
    put $ s { varMap =
        Map.insert x (vi { delayedConstraints = cs >> constraint }) vm }

type BinaryConstraint s = Int -> Int -> Solving s ()
addBinaryConstraint :: BinaryConstraint s -> BinaryConstraint s
addBinaryConstraint f x y = do
    let constraint  = f x y
    constraint
    addConstraint x constraint
    addConstraint y constraint


-- Commit to the first substitution of a given constraint variable
firstSubst :: CVar -> Solving s PTerm
firstSubst var = do
  vals <- lookupDom var
  let PTerm f sigma = head vals
  let newval = PTerm f (injPSubst (fstSubst sigma))
  when ([newval] /= vals) $ update var [newval]
  return newval








