module Main where

import Control.Monad.Except
import Control.Monad.State
import System.Environment
import qualified Data.Map as Map
import Data.Either

import Prel
import Data
import Poset
-- import Solver
-- import SimpleSolver
-- import CompSolver
import Formula
import Examples
import Parser


solver :: Cube -> Boundary -> Bool -> IO ()
solver cube goal verbose = do
  putStrLn "CUBE"
  mapM_ print (constr cube)
  putStrLn "GOAL"
  print goal

  if not (wellFormed cube)
    then return ()
    else do
      case findDistortion cube goal of
        Just t -> do
          putStrLn "FOUND SIMPLE SOLUTIONS"
          (putStrLn . agdaTerm) t
        Nothing ->
          return ()


  -- RUN KAN COMPOSITION SOLVER
  -- if not (null simp)
  --   then do
  --     putStrLn "FOUND SIMPLE SOLUTIONS"
  --     mapM_ (putStrLn . agdaTerm) simp
  --   else do
  --     putStrLn "NO SIMPLE SOLUTIONS"
  --     comp <- runExceptT $ runStateT compSolve (mkSEnv cube goal verbose)
  --     case comp of
  --       Right res -> do
  --         putStrLn "FOUND COMPOSITION SOLUTIONS"
  --         mapM_ (putStrLn . agdaTerm) (fst res)
  --       Left _ -> do
  --         putStrLn "NO COMPOSITION SOLUTIONS"
  --     return ()

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




