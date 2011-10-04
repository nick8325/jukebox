module Main where

import Control.Monad
import Options
import Control.Applicative
import Data.Monoid
import Toolbox

tools = mconcat [tofof, clausify]

tofof = tool info pipeline
  where
    info = Tool "ToFOF" "1" "Translate from TFF to FOF"
    pipeline =
      allFilesBox info <*>
        (parseProblemBox =>>
         toFofBox =>>
         prettyPrintBox "fof")

clausify = tool info pipeline
  where
    info = Tool "Clausify" "1" "Clausify a problem"
    pipeline =
      allFilesBox info <*>
        (parseProblemBox =>>
         clausifyBox =>>
         prettyPrintBox "cnf")

main = join (parseCommandLine (Tool "Jukebox" "1" undefined) tools)