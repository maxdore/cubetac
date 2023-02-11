module Main where

import Control.Monad.Except
import Control.Monad.State
import System.Environment
import qualified Data.Map as Map
import Data.Either
import qualified Data.Text as T
-- import Text.Regex

import Debug.Trace

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
  -- print (preprocess stdin)
  (context,goal) <- parseAgdaProblem (preprocess stdin)
  -- putStrLn $ show context
  -- putStrLn $ show goal
  solver context goal False
  return ()

fileproblem file = do
  stdin <- readFile file
  putStrLn stdin
  print (preprocess stdin)
  (context,goal) <- parseAgdaProblem (preprocess stdin)
  putStrLn $ show context
  putStrLn $ show goal
  solver context goal True
  return ()


trim :: String -> String
trim [] = []
trim (' ' : ' ' : xs) = trim (' ' : xs)
trim (x:xs) = x : trim xs

preprocess :: String -> T.Text
preprocess str =
  let raw = T.pack (trim str) in
  let delim = T.pack "\n---\n" in
  let [ctxt, goal] = T.splitOn delim raw in
  let goal1line = T.pack (trim (T.unpack (T.replace (T.pack "\n") (T.pack " ") goal))) in
  T.concat [ctxt , delim , goal1line]

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




