{-# LANGUAGE OverloadedStrings #-}
module AgdaShow where

import System.Process.Typed
import Control.Monad.Except
import qualified Data.ByteString.Lazy as Byte
import qualified Data.ByteString.Lazy.Search as ByteS

import Data.String
import Data.List
import Data.Ord
import qualified Data.Text.Lazy             as TL
import qualified Data.Text.Lazy.Encoding    as TL
import qualified Data.Text.Lazy.IO          as TL


