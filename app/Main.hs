module Main where

import System.Environment
import System.IO

import Core
import Examples
import Benchmark

main :: IO ()
main = runbenchmark
-- main = do
--   args <- getArgs
--   let file = args !! 0
--   let gid = args !! 1
--   let verbose = "verbose" `elem` args

--   (cube , goals) <- loadExample file
--   case lookup gid goals of
--     Just goal -> solver cube goal verbose
--     Nothing -> error $ "Could not find definition of " ++ gid




