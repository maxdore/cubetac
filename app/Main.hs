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


main :: IO ()
main = return ()

solver :: Cube -> Boundary -> IO ()
solver cube goal = do
  putStrLn "CUBE"
  mapM_ print (constr cube)
  putStrLn "GOAL"
  print goal

  putStrLn "RUN SIMPLE SOLVER"
  simp <- concatMap fst . rights <$>
    mapM
      (\(Decl f _) -> runExceptT $ runStateT (simpleSolve f) (mkSEnv cube goal False))
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
