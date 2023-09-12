{-# LANGUAGE BangPatterns #-}

module Benchmark where

import System.CPUTime
import System.Timeout

import Core
import Poset
import Examples
import Rulesets.Cart
import Rulesets.Dede
import Rulesets.Cont
import Rulesets.Disj
import Rulesets.DeMo

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
  , ("associativity2", threep , assoc2)
  , ("assocOr", threep , assocOr)
  , ("assocAnd", threep , assocAnd)
  , ("EH square", higherpq , ehSquare)
  , ("EH direct", higherpq , eckmannHilton)
  , ("assoc single vert", threep' , assoc')
        ]

carttests = tests :: [(String,Ctxt Cart Cart, Ty Cart Cart)]
dedetests = tests :: [(String,Ctxt Dede PSubst, Ty Dede PSubst)]
conttests = tests :: [(String,Ctxt Cont PCont, Ty Cont PCont)]
conjtests = tests :: [(String,Ctxt Conj PSubst, Ty Conj PSubst)]
disjtests = tests :: [(String,Ctxt Disj PSubst, Ty Disj PSubst)]
demotests = tests :: [(String,Ctxt DeMo DeMo, Ty DeMo DeMo)]

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
  putStrLn $ "                   | " ++ concatMap (\s -> padc s 9 ++ " | ") ["Cartesian","Dedekind","Contort","Conj","Disj", "DeMorgan"]
  putStrLn (replicate (20+6*12) '-')
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
            putStrLn ""
          ) [0..length carttests - 1]
  return ()
