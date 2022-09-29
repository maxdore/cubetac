module Main where

import Control.Monad.Except
import Control.Monad.State
import System.Environment
import qualified Data.Map as Map

import Prel
import Data
import Deg
import Type
import Solver
import Examples

-- runSolve :: SEnv s -> IO (Either String ([Term],SEnv s))
-- runSolve env = do
--   res <- runExceptT $ runStateT solve env
--   case res of
--     Left err -> do
--       putStrLn $ "ERROR: " ++ err
--     Right (t , _)-> do
--       putStrLn "SUCCESS"
--       putStrLn $ show t
--   return res




main :: IO ()
main = return ()
