module Main where

import Control.Monad
import Jukebox.Options
import Control.Applicative
import Data.Monoid
import Jukebox.Toolbox

tools = mconcat [fof, cnf, monotonox, guessmodel]

fof = tool info pipeline
  where
    info = Tool "fof" "Jukebox TFF-to-FOF translator" "1"
                "Translate from TFF (typed) to FOF (untyped)"
    pipeline =
      greetingBox info =>>
      allFilesBox <*>
        (parseProblemBox =>>=
         toFofBox =>>=
         prettyPrintBox)

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
         prettyClauseBox)

justparser = tool info pipeline
  where
    info = Tool "parser" "Parser" "1"
                "Just parse the problem"
    pipeline =
      greetingBox info =>>
      allFilesBox <*>
        (parseProblemBox =>>=
         clausifyBox =>>=
         oneConjectureBox =>>=
         inferBox =>>=
         printInferredBox =>>=
         annotateMonotonicityBox =>>=
         prettyPrintBox)

guessmodel = tool info pipeline
  where
    info = Tool "guessmodel" "Infinite model guesser" "1"
                "Guess an infinite model"
    pipeline =
      greetingBox info =>>
      allFilesBox <*>
        (parseProblemBox =>>=
         guessModelBox =>>=
         prettyPrintBox)

equinox = tool info pipeline
  where
    info = Tool "equinox" "Equinox" "7"
                "Prove a first-order problem"
    pipeline =
      greetingBox info =>>
      allFilesBox <*>
        (parseProblemBox =>>=
         clausifyBox =>>=
         allObligsBox <*> equinoxBox)

jukebox = Tool "jukebox" "Jukebox" "1"
               "A first-order logic toolbox"

main = join (parseCommandLine jukebox tools)
