module Main where

import Control.Monad
import Options
import Control.Applicative
import Data.Monoid
import Toolbox

tools = mconcat [monotonox, clausify]

monotonox = tool info pipeline
  where
    info = Tool "Monotonox" "1" "Monotonicity analysis"
    pipeline =
      allFilesBox info <*>
        (parseProblemBox =>>
         clausifyBox =>>
         monotonicityBox)

clausify = tool info pipeline
  where
    info = Tool "Clausify" "1" "Clausify a problem"
    pipeline =
      allFilesBox info <*>
        (parseProblemBox =>>
         clausifyBox =>>
         prettyPrintBox)

main = join (parseCommandLine (Tool "Jukebox" "1" undefined) tools)