{-# LANGUAGE CPP #-}
module Main where

import Control.Monad
import Jukebox.Options
import Jukebox.Toolbox
#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
import Data.Monoid
#endif

tools = mconcat [fof, cnf, smt, monotonox, guessmodel]

fof = tool info pipeline
  where
    info = Tool "fof" "Jukebox TFF-to-FOF translator" "1"
                "Translate from TFF (typed) to FOF (untyped)"
    pipeline =
      greetingBox info =>>
      allFilesBox <*>
        (parseProblemBox =>>=
         toFofBox =>>=
         prettyPrintProblemBox)

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

smt = tool info pipeline
  where
    info = Tool "smt" "Jukebox TFF-to-SMTLIB translator" "1"
                "Translate from TFF to SMTLIB"
    pipeline =
      greetingBox info =>>
      allFilesBox <*>
        (parseProblemBox =>>=
         prettyPrintProblemSMTBox)

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
         prettyPrintClausesBox)

guessmodel = tool info pipeline
  where
    info = Tool "guessmodel" "Infinite model guesser" "1"
                "Guess an infinite model"
    pipeline =
      greetingBox info =>>
      allFilesBox <*>
        (parseProblemBox =>>=
         guessModelBox =>>=
         prettyPrintProblemBox)

jukebox = Tool "jukebox" "Jukebox" "1"
               "A first-order logic toolbox"

main = join (parseCommandLine jukebox tools)
