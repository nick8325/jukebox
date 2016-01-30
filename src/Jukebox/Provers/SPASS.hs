{-# LANGUAGE GADTs #-}
module Jukebox.Provers.SPASS where

import Jukebox.Form hiding (tag, Or)
import Jukebox.Options
import Jukebox.Utils
import Jukebox.TPTP.Print

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

runSPASS :: SPASSFlags -> Problem Form -> IO Answer
runSPASS flags prob
  | not (isFof prob) = error "runSPASS: SPASS doesn't support many-typed problems"
  | otherwise = do
    (_code, str) <- popen (spass flags) spassFlags (showProblem prob)
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
