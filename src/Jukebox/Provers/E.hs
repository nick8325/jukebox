{-# LANGUAGE GADTs #-}
module Jukebox.Provers.E where

import Jukebox.Form hiding (tag, Or)
import Jukebox.Name
import Jukebox.Options
import Control.Applicative hiding (Const)
import Control.Monad
import Jukebox.Utils
import Jukebox.TPTP.Parsec hiding (run)
import Jukebox.TPTP.Parse.Core hiding (newFunction, Term)
import Jukebox.TPTP.Print
import Jukebox.TPTP.Lexer hiding (Normal, keyword, Axiom, Var, Theorem)
import Data.Maybe
import qualified Data.Map.Strict as Map
import Data.Map(Map)

data EFlags = EFlags {
  eprover :: String,
  timeout :: Maybe Int,
  memory :: Maybe Int
  }

eflags =
  inGroup "E prover options" $
  EFlags <$>
    flag "eprover"
      ["Path to the E theorem prover.",
       "Default: eprover"]
      "eprover"
      argFile <*>
    flag "timeout"
      ["Timeout for E, in seconds.",
       "Default: (off)"]
      Nothing
      (fmap Just argNum) <*>
    flag "memory"
      ["Memory limit for E, in megabytes.",
       "Default: (off)"]
      Nothing
      (fmap Just argNum)

-- Work around bug in E answer coding.
mangleAnswer :: Symbolic a => a -> NameM a
mangleAnswer t =
  case typeOf t of
    Term -> term t
    _ -> recursivelyM mangleAnswer t
  where term (f :@: [t]) | base f == "$answer" = do
          wrap <- newFunction "answer" [typ t] (head (funArgs f))
          return (f :@: [wrap :@: [t]])
        term t = recursivelyM mangleAnswer t

runE :: EFlags -> Problem Form -> IO (Either Answer [Term])
runE flags prob
  | not (isFof prob) = error "runE: E doesn't support many-typed problems"
  | otherwise = do
    (_code, str) <- popen (eprover flags) eflags
                   (showProblem (run prob mangleAnswer))
    return (extractAnswer prob str)
  where eflags = [ "--soft-cpu-limit=" ++ show n | Just n <- [timeout flags] ] ++
                 ["--memory-limit=" ++ show n | Just n <- [memory flags] ] ++
                 ["--tstp-in", "--tstp-out", "-tAuto", "-xAuto"] ++
                 ["-l", "0"]

extractAnswer :: Symbolic a => a -> String -> Either Answer [Term]
extractAnswer prob str = fromMaybe (Left status) (fmap Right answer)
  where varMap = Map.fromList [(show (name x), x) | x <- vars prob]
        funMap = Map.fromList [(show (name x), x) | x <- functions prob]
        result = lines str
        status = head $
          [Sat Satisfiable | "# SZS status Satisfiable" <- result] ++
          [Sat CounterSatisfiable | "# SZS status CounterSatisfiable" <- result] ++
          [Unsat Unsatisfiable | "# SZS status Unsatisfiable" <- result] ++
          [Unsat Theorem | "# SZS status Theorem" <- result] ++
          [NoAnswer Timeout | "# SZS status ResourceOut" <- result] ++
          [NoAnswer Timeout | "# SZS status Timeout" <- result] ++
          [NoAnswer Timeout | "# SZS status MemyOut" <- result] ++
          [NoAnswer GaveUp]
        answer = listToMaybe $
          [ parse xs
          | line <- result
          , let prefix = "# SZS answers Tuple ["
                suffix = "|_]"
                (prefix', mid) = splitAt (length prefix) line
                (xs, suffix') = splitAt (length mid - length suffix) mid
          , prefix == prefix'
          , suffix == suffix' ]
        parse xs =
          let toks = scan xs
          in case run_ parser (UserState (initialState Nothing) toks) of
            Ok _ ts -> ts
            _ -> error "runE: couldn't parse result from E"
        parser =
          parens (bracks term `sepBy1` punct Or)
          <|> fmap (:[]) (bracks term)
        term =
          fmap (Var . lookup varMap) variable <|>
          liftM2 (:@:) (fmap (lookup funMap) atom) terms
        terms =
          bracks (term `sepBy1` punct Comma)
          <|> return []
        lookup :: Ord a => Map String a -> String -> a
        lookup m x = Map.findWithDefault (error "runE: result from E mentions free names") x m
