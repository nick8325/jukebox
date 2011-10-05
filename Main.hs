module Main where

import Control.Monad
import Options
import Control.Applicative
import Data.Monoid
import Toolbox

tools = mconcat [fof, cnf, monotonox]

fof = tool info pipeline
  where
    info = Tool "fof" "Jukebox TFF-to-FOF translator" "1"
                "Translate from TFF to FOF"
    pipeline =
      allFilesBox info <*>
        (parseProblemBox =>>
         toFofBox =>>
         prettyPrintBox "fof")

monotonox = tool info pipeline
  where
    info = Tool "monotonox" "Monotonox" "1"
                "Monotonicity analysis"
    pipeline =
      allFilesBox info <*>
        (parseProblemBox =>>
         clausifyBox =>>
         monotonicityBox =>>
         writeFileBox)

cnf = tool info pipeline
  where
    info = Tool "cnf" "Jukebox clausifier" "1"
                "Clausify a problem"
    pipeline =
      allFilesBox info <*>
        (parseProblemBox =>>
         clausifyBox =>>
         prettyPrintBox "cnf")

jukebox = Tool "jukebox" "Jukebox" "1"
               "A first-order logic toolbox"

main = join (parseCommandLine jukebox tools)