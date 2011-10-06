module Main where

import Control.Monad
import Options
import Control.Applicative
import Data.Monoid
import Toolbox
import ParadoxParser.Convert(form)
import TPTP.FindFile
import ParadoxParser.Test

tools = mconcat [fof, cnf, monotonox, testparser]

fof = tool info pipeline
  where
    info = Tool "fof" "Jukebox TFF-to-FOF translator" "1"
                "Translate from TFF to FOF"
    pipeline =
      greetingBox info =>>
      allFilesBox <*>
        (parseProblemBox =>>=
         toFofBox =>>=
         prettyPrintBox <*> pure "fof")

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

testparser = tool info pipeline
  where
    info = Tool "testparser" "Parser test" "1"
                "Compare Jukebox and Paradox parding"
    pipeline =
      greetingBox info =>>
      allFilesBox <*> (testParserIO <$> findFileFlags <*> printBoth)

    printBoth =
      bool "print-both" ["Print problems when there is a difference between them"]

jukebox = Tool "jukebox" "Jukebox" "1"
               "A first-order logic toolbox"

main = join (parseCommandLine jukebox tools)