{-# LANGUAGE BangPatterns #-}

module Benchmark where

-- import Data.Time
import System.CPUTime

import Core
import Examples
import Deg
import Conn
import Cont


tests :: Rs r w => [(String,Ctxt r w, Ty r w)]
tests = [
    ("orsquare", twop, orGoal)
  , ("andsquare", twop , andGoal)
  , ("pqpq square", twop , pqpq)
  , ("right unit law", twop , unitr)
  , ("left unit law", twop , unitl)
  , ("assocback", threep , assocback)
  , ("assocright", threep , assocright)
  -- , ("associativity", threep , assoc)
        ]

degtests = tests :: [(String,Ctxt Deg Deg, Ty Deg Deg)]
conntests = tests :: [(String,Ctxt ConnFormula PPM, Ty ConnFormula PPM)]
conttests = tests :: [(String,Ctxt Cont PCont, Ty Cont PCont)]

time :: Rs r w => Ctxt r w -> Ty r w -> IO ()
time c ty = do
  start <- getCPUTime
  let !r = findComp c ty
  end <- getCPUTime
  let diff = (end - start) `div` 1000000000
  putStr (padr (show diff ++ "ms") 9)
  return ()


padr x n = replicate (n - length x) ' ' ++ x
padl x n = x ++ replicate (n - length x) ' '
padc x n = let m = (n - length x) in replicate (m `div` 2 + m `mod` 2) ' ' ++ x ++ replicate (m `div` 2) ' '

main :: IO ()
main = do
  putStrLn $ "                   | " ++ concatMap (\s -> padc s 9 ++ " | ") ["Deg","Conn","Cont"]
  putStrLn (replicate (20+3*12) '-')
  mapM_ (\i -> do
            let (name , degc , degty) = degtests!!i
            putStr (padr name 18 ++ " | ")
            time degc degty
            putStr " | "
            let (_ , connc , connty) = conntests!!i
            time connc connty
            putStr " | "
            let (_ , contc , contty) = conttests!!i
            time contc contty
            putStr " | "
            putStrLn ""
          ) [0..length degtests - 1]
  return ()
