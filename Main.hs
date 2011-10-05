module Main where

import Control.Monad
import Options
import Control.Applicative
import Data.Monoid
import Toolbox

tools = mconcat [fof, cnf, monotonox]

fof = tool info pipeline
  where
    info = Tool "FOF" "1" "Translate from TFF to FOF"
    pipeline =
      allFilesBox info <*>
        (parseProblemBox =>>
         toFofBox =>>
         prettyPrintBox "fof")

monotonox = tool info pipeline
  where
    info = Tool "Monotonox" "1" "Monotonicity analysis"
    pipeline =
      allFilesBox info <*>
        (parseProblemBox =>>
         clausifyBox =>>
         monotonicityBox =>>
         writeFileBox)

cnf = tool info pipeline
  where
    info = Tool "CNF" "1" "Clausify a problem"
    pipeline =
      allFilesBox info <*>
        (parseProblemBox =>>
         clausifyBox =>>
         prettyPrintBox "cnf")

main = join (parseCommandLine (Tool "Jukebox" "1" undefined) tools)