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
      greetingBox info =>>
      allFilesBox <*>
        (parseProblemBox =>>=
         toFofBox =>>=
         prettyPrintBox "fof")

monotonox = tool info pipeline
  where
    info = Tool "monotonox" "Monotonox" "1"
                "Monotonicity analysis"
    pipeline =
      greetingBox info =>>
      allFilesBox <*>
        (parseProblemBox =>>=
         clausifyBox =>>=
         oneConjectureBox =>>=
         monotonicityBox =>>=
         writeFileBox)

cnf = tool info pipeline
  where
    info = Tool "cnf" "Jukebox clausifier" "1"
                "Clausify a problem"
    pipeline =
      greetingBox info =>>
      allFilesBox <*>
        (parseProblemBox =>>=
         clausifyBox =>>=
         oneConjectureBox =>>=
         prettyPrintBox "cnf")

jukebox = Tool "jukebox" "Jukebox" "1"
               "A first-order logic toolbox"

main = join (parseCommandLine jukebox tools)