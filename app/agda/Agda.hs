module Agda.Agda where

import Control.Monad.Except
import Control.Monad.State
import System.Environment
import qualified Data.Map as Map
import qualified Data.Text as T

import Prel
import Poset
import Data


solver :: [a] -> b -> T.Text
solver ctxt goal = T.pack "zero"
