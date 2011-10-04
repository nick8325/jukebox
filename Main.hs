{-# LANGUAGE BangPatterns #-}
module Main where

import TPTP.ParseProblem
import System.Environment
import Form
-- import InferTypes
import TPTP.Print
import Name
import Text.PrettyPrint.HughesPJ
import Clausify
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL
import Control.Monad
import Monotonox.Monotonicity
import NameMap
import TPTP.Binary
import TPTP.FindFile
import Options
import Control.Applicative
import System.Exit
import Toolbox

data Flags = Flags ClausifyFlags [FilePath] [FilePath] deriving Show

monotonox = Tool "Monotonox" "1" "Monotonicity analysis"
jukebox = Tool "Jukebox" "1" undefined

tools = tool monotonox pipeline

pipeline :: OptionParser (IO ())
pipeline =
  allFilesTool monotonox <*>
  (parseProblemTool =>>
   clausifyTool =>>
   monotonicityTool)

main = join (parseCommandLine jukebox tools)