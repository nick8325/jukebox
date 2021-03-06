{-# LANGUAGE GADTs, CPP #-}
module Jukebox.ExternalProvers.SPASS where

import Jukebox.Form hiding (tag, Or)
import Jukebox.Options
import Jukebox.Utils
import Jukebox.TPTP.Print
#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif

data SPASSFlags =
  SPASSFlags {
    spass   :: String,
    timeout :: Maybe Int,
    sos     :: Bool }

spassFlags =
  inGroup "SPASS prover options" $
  SPASSFlags <$>
    flag "spass"
      ["Path to SPASS (\"SPASS\" by default)."]
      "SPASS"
      argFile <*>
    flag "timeout"
      ["Timeout in seconds (off by default)."]
      Nothing
      (fmap Just argNum) <*>
    flag "sos"
      ["Use set-of-support strategy (off by default)."]
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
    [ Unsat Unsatisfiable Nothing | "SPASS beiseite: Proof found." <- lines result ] ++
    [ Sat Satisfiable Nothing     | "SPASS beiseite: Completion found." <- lines result ] ++
    [ NoAnswer Timeout ]
