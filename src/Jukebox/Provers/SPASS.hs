{-# LANGUAGE GADTs #-}
module Jukebox.Provers.SPASS where

import Jukebox.Form hiding (tag, Or)
import Jukebox.Name
import Jukebox.Options
import Control.Applicative hiding (Const)
import Control.Monad
import Jukebox.Utils
import Jukebox.TPTP.Parsec
import Jukebox.TPTP.ClauseParser hiding (newFunction, Term)
import Jukebox.TPTP.Print
import Jukebox.TPTP.Lexer hiding (Normal, keyword, Axiom, name, Var)
import Text.PrettyPrint.HughesPJ hiding (parens)
import Data.Maybe
import qualified Data.Map.Strict as Map
import Data.Map(Map)
import Data.Hashable
import System.Exit

data SPASSFlags =
  SPASSFlags {
    spass   :: String,
    timeout :: Maybe Int,
    sos     :: Bool }

spassFlags =
  inGroup "SPASS prover options" $
  SPASSFlags <$>
    flag "spass"
      ["Path to SPASS.",
       "Default: SPASS"]
      "SPASS"
      argFile <*>
    flag "timeout"
      ["Timeout in seconds.",
       "Default: (none)"]
      Nothing
      (fmap Just argNum) <*>
    flag "sos"
      ["Use set-of-support strategy.",
       "Default: false"]
      False
      (pure True)

runSPASS :: (Pretty a, Symbolic a) => SPASSFlags -> Problem a -> IO Answer
runSPASS flags prob
  | not (isFof (open prob)) = error "runSPASS: SPASS doesn't support many-typed problems"
  | otherwise = do
    (code, str) <- popen (spass flags) spassFlags
                   (render (prettyProblem "cnf" Normal prob))
    return (extractAnswer str)
  where
    spassFlags =
      ["-TimeLimit=" ++ show n | Just n <- [timeout flags] ] ++
      ["-SOS" | sos flags] ++
      ["-TPTP", "-Stdin"]

extractAnswer :: String -> Answer
extractAnswer result =
  head $
    [ Unsatisfiable    | "SPASS beiseite: Proof found." <- lines result ] ++
    [ Satisfiable      | "SPASS beiseite: Completion found." <- lines result ] ++
    [ NoAnswer Timeout ]
