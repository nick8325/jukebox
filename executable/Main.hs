{-# LANGUAGE CPP #-}
module Main where

import Control.Monad
import Jukebox.Options
import Jukebox.Toolbox
#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
import Data.Monoid
#endif
import Data.List
import System.Exit
import System.Environment

main = do
  prog <- getProgName
  args <- getArgs
  let
    progTool = prog ++ " <toolname>"
    help =
      printHelp ExitSuccess $
        intercalate [""] $
          [usageText progTool "Jukebox, a first-order logic toolbox"] ++
          [["<toolname> can be any of the following:"] ++
           [ "  " ++ name tool ++ " - " ++ description tool
           | tool <- tools, name tool `notElem` map name internal ]] ++
          [["For more information about each tool, run " ++ progTool ++ " --help."]]
    usage msg = printError prog msg
  case args of
    [] -> help
    ["--help"] -> help
    ["--version"] ->
      putStrLn $ "Jukebox version " ++ VERSION_jukebox
    (('-':_):_) -> usage "Expected a tool name as first argument"
    (arg:args) ->
      case [tool | tool <- tools, name tool == arg] of
        [] -> usage ("No such tool " ++ arg)
        [tool] ->
          join $
            parseCommandLineWithArgs
              (prog ++ " " ++ name tool) args (description tool) (pipeline tool)

data Tool =
  Tool {
    name :: String,
    description :: String,
    pipeline :: OptionParser (IO ()) }

tools = [fof, cnf, smt, monotonox, guessmodel]
internal = [guessmodel]

fof =
  Tool "fof" "Translate a problem from TFF (typed) to FOF (untyped)" $
    allFilesBox <*>
      (parseProblemBox =>>=
       toFofBox =>>=
       prettyPrintProblemBox)

monotonox =
  Tool "monotonox" "Analyse a problem for monotonicity" $
    allFilesBox <*>
      (parseProblemBox =>>=
       clausifyBox =>>=
       oneConjectureBox =>>=
       monotonicityBox =>>=
       writeFileBox)

smt =
  Tool "smt" "Translate a problem from TPTP format to SMTLIB format" $
    allFilesBox <*>
      (parseProblemBox =>>=
       prettyPrintProblemSMTBox)

cnf =
  Tool "cnf" "Clausify a TPTP (TFF or FOF) problem" $
    allFilesBox <*>
      (parseProblemBox =>>=
       clausifyBox =>>=
       oneConjectureBox =>>=
       prettyPrintClausesBox)

guessmodel =
  Tool "guessmodel" "Guess an infinite model (internal use)" $
    allFilesBox <*>
      (parseProblemBox =>>=
       guessModelBox =>>=
       prettyPrintProblemBox)
