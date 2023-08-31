{-# LANGUAGE BangPatterns #-}

module Benchmark where

import System.CPUTime
import System.Timeout

import Core
import Examples
import Rulesets.Cart
import Rulesets.Dede
import Rulesets.Cont
import Rulesets.Disj


tests :: Rs r w => [(String,Ctxt r w, Ty r w)]
tests = [
    ("orsquare", twop, orGoal)
  , ("andsquare", twop , andGoal)
  , ("pqpq square", twop , pqpq)
  , ("right unit law", twop , unitr)
  , ("left unit law", twop , unitl)
  , ("assocback", threep , assocback)
  , ("assocright", threep , assocright)
  , ("associativity", threep , assoc)
  , ("EH square", higherpq , ehSquare)
        ]

carttests = tests :: [(String,Ctxt Cart Cart, Ty Cart Cart)]
dedetests = tests :: [(String,Ctxt Dede PPM, Ty Dede PPM)]
conttests = tests :: [(String,Ctxt Cont PCont, Ty Cont PCont)]
conjtests = tests :: [(String,Ctxt Conj Conj, Ty Conj Conj)]
disjtests = tests :: [(String,Ctxt Disj Disj, Ty Disj Disj)]

time :: Rs r w => Ctxt r w -> Ty r w -> IO ()
time c ty = do
  start <- getCPUTime
  comp <- timeout (10 * 1000000) (do
    let !r = findComp c ty
    return ())
  case comp of
    Just res -> do
      end <- getCPUTime
      let diff = (end - start) `div` 1000000000
      putStr (padr (show diff ++ "ms") 9)
      return ()
    Nothing -> putStr "  TIMEOUT"


padr x n = replicate (n - length x) ' ' ++ x
padl x n = x ++ replicate (n - length x) ' '
padc x n = let m = (n - length x) in replicate (m `div` 2 + m `mod` 2) ' ' ++ x ++ replicate (m `div` 2) ' '

main :: IO ()
main = do
  putStrLn $ "                   | " ++ concatMap (\s -> padc s 9 ++ " | ") ["Cart","Dede","Cont","Conj","Disj"]
  putStrLn (replicate (20+5*12) '-')
  mapM_ (\i -> do
            let (name , cartc , cartty) = carttests!!i
            putStr (padr name 18 ++ " | ")
            time cartc cartty
            putStr " | "
            let (_ , dedec , dedety) = dedetests!!i
            time dedec dedety
            putStr " | "
            let (_ , contc , contty) = conttests!!i
            time contc contty
            putStr " | "
            let (_ , conjc , conjty) = conjtests!!i
            time conjc conjty
            putStr " | "
            let (_ , disjc , disjty) = disjtests!!i
            time disjc disjty
            putStr " | "
            putStrLn ""
          ) [0..length carttests - 1]
  return ()
