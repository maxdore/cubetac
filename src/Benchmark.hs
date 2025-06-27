{-# LANGUAGE BangPatterns #-}

module Benchmark where

import System.CPUTime
import System.Timeout

import Core
import Poset
import Examples
import Rulesets.Cart
import Rulesets.Dede
import Rulesets.PMap
import Rulesets.Disj
import Rulesets.DeMo
import Rulesets.TruthTable

tests :: Rs r w => [(String,Ctxt r w, Ty r w)]
tests = [
    ("invert", twop, invGoal)
  , ("orsquare", twop, orGoal)
  , ("andsquare", twop , andGoal)
  , ("pqpq square", twop , pqpq)
  , ("right unit law", twop , unitr)
  , ("left unit law", twop , unitl)
  , ("assocback", threep , assocback)
  , ("assocright", threep , assocright)
  , ("associativity", threep , assoc)
  , ("associativity2", threep , assoc2)
  , ("assocOr", threep , assocOr)
  , ("assocAnd", threep , assocAnd)
  , ("EH square", higherpq , ehSquare)
  , ("EH direct", higherpq , eckmannHilton)
  , ("assoc single vert", threep' , assoc')
        ]

carttests = tests :: [(String,Ctxt Cart Cart, Ty Cart Cart)]
dedetests = tests :: [(String,Ctxt Dede PPMap, Ty Dede PPMap)]
conttests = tests :: [(String,Ctxt PMap PPMap, Ty PMap PPMap)]
conjtests = tests :: [(String,Ctxt Conj PPMap, Ty Conj PPMap)]
disjtests = tests :: [(String,Ctxt Disj PPMap, Ty Disj PPMap)]
demotests = tests :: [(String,Ctxt DeMo DeMo, Ty DeMo DeMo)]
demotttests = tests :: [(String,Ctxt TruthTable PTruthTable, Ty TruthTable PTruthTable)]

time :: Rs r w => Ctxt r w -> Ty r w -> IO ()
time c ty = do
  start <- getCPUTime
  comp <- timeout (10 * 100000) (do
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

runbenchmark :: IO ()
runbenchmark = do
  putStrLn $ "                   | " ++ concatMap (\s -> padc s 9 ++ " | ") ["Cartesian","Dedekind","Posetmap","Conj","Disj", "DeMorgan", "DeMo TT"]
  putStrLn (replicate (20+7*12) '-')
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
            let (_ , democ , demoty) = demotests!!i
            time democ demoty
            putStr " | "
            let (_ , demottc , demottty) = demotttests!!i
            time demottc demottty
            putStr " | "
            putStrLn ""
          ) [0..length carttests - 1]
  return ()
