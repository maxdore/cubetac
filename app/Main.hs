module Main where

import Control.Monad.Except
import Control.Monad.State
import System.Environment
import qualified Data.Map as Map
import Data.Either

import Prel
import Data
import Poset
import Solver
import SimpleSolver
import Formula
import Examples
import Parser


solver :: Cube -> Boundary -> Bool -> IO ()
solver cube goal verbose = do
  putStrLn "CUBE"
  mapM_ print (constr cube)
  putStrLn "GOAL"
  print goal

  putStrLn "RUN SIMPLE SOLVER"
  simp <- concatMap fst . rights <$>
    mapM
      (\(Decl f _) -> runExceptT $ runStateT (simpleSolve f) (mkSEnv cube goal verbose))
      (constr cube)

  -- RUN KAN COMPOSITION SOLVER
  if not (null simp)
    then do
      putStrLn "FOUND SIMPLE SOLUTIONS"
      mapM_ (putStrLn . agdaTerm) simp
    else do
      putStrLn "NO SIMPLE SOLUTIONS"
      -- res <- runExceptT $ runStateT (comp goal) (mkSEnv cube goal)
      return ()

  return ()



main :: IO ()
main = do
  args <- getArgs
  let file = args !! 0
  let gid = args !! 1
  let verbose = "verbose" `elem` args

  (cube , goals) <- loadExample file
  case lookup gid goals of
    Just goal -> solver cube goal verbose
    Nothing -> error $ "Could not find definition of " ++ gid




