module Main where

import Control.Monad.Except
import Control.Monad.State
import System.Environment
import qualified Data.Map as Map
import Data.Either
import qualified Data.Text as T

import System.IO

import Prel
import Data
import Poset
import Solver
import Formula
import Examples
import PathParser


solver :: Cube -> Boundary -> Bool -> IO ()
solver cube goal verbose = do
  -- putStrLn "CUBE"
  -- mapM_ print (constr cube)
  -- putStrLn "GOAL"
  -- print goal

  if not True -- (wellFormed cube)
    then return ()
    else do
      case findContortion cube goal of
        Just t -> do
          when verbose (putStrLn "FOUND SIMPLE SOLUTIONS")
          when verbose (print t)
          (putStrLn . agdaTerm) t
        Nothing ->
          return ()



  return ()

main = do
  stdin <- getContents
  -- putStrLn stdin
  (context,goal) <- parseAgdaProblem (T.pack stdin)
  -- putStrLn $ show context
  -- putStrLn $ show goal
  solver context goal False
  return ()


fileproblem file = do
  stdin <- readFile file
  putStrLn stdin
  (context,goal) <- parseAgdaProblem (T.pack stdin)
  putStrLn $ show context
  putStrLn $ show goal
  solver context goal True
  return ()

-- main :: IO ()
-- main = do
--   args <- getArgs
--   let file = args !! 0
--   let gid = args !! 1
--   let verbose = "verbose" `elem` args

--   (cube , goals) <- loadExample file
--   case lookup gid goals of
--     Just goal -> solver cube goal verbose
--     Nothing -> error $ "Could not find definition of " ++ gid




