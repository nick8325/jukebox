{-# LANGUAGE GADTs #-}
module Provers.E where

import Form hiding (tag, Or)
import Name
import Options
import Control.Applicative hiding (Const)
import Control.Monad
import Utils
import TPTP.Parsec
import TPTP.ClauseParser hiding (newFunction, Term)
import TPTP.Print
import TPTP.Lexer hiding (Normal, keyword, Axiom, name, Var)
import Text.PrettyPrint.HughesPJ hiding (parens)
import Data.Maybe
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL
import qualified Seq as S
import qualified Map
import Map(Map)
import Data.Hashable

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
  where term (f :@: [t]) | stringBaseName f == "$answer" = do
          wrap <- newFunction "answer" [typ t] (head (funArgs f))
          return (f :@: [wrap :@: [t]])
        term t = recursivelyM mangleAnswer t

runE :: (Pretty a, Symbolic a) => EFlags -> Problem a -> IO (Either Answer [Term])
runE flags prob
  | not (isFof (open prob)) = error "runE: E doesn't support many-typed problems"
  | otherwise = do
    res <- popen (eprover flags) eflags
           (BS.pack (render (prettyProblem "fof" Normal (close prob mangleAnswer))))
    case res of
      Left code -> error $ "runE: E failed with exit code " ++ show code
      Right str -> return (extractAnswer (open prob) (BS.unpack str))
  where eflags = [ "--soft-cpu-limit=" ++ show n | Just n <- [timeout flags] ] ++
                 ["--memory-limit=" ++ show n | Just n <- [memory flags] ] ++
                 ["--tstp-in", "--tstp-out", "-tAuto", "-xAuto"] ++
                 ["-l", "0"]

extractAnswer :: Symbolic a => a -> String -> Either Answer [Term]
extractAnswer prob str = fromMaybe (Left status) (fmap Right answer)
  where env = uniquify (S.unique (names prob))
        varMap = Map.fromList [(env (name x), x) | x <- vars prob]
        funMap = Map.fromList [(env (name x), x) | x <- functions prob]
        result = lines str
        status = head $
          [Satisfiable | "# SZS status Satisfiable" <- result] ++ 
          [Satisfiable | "# SZS status CounterSatisfiable" <- result] ++
          [Unsatisfiable | "# SZS status Unsatisfiable" <- result] ++
          [Unsatisfiable | "# SZS status Theorem" <- result] ++ 
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
                (suffix', xs) = splitAt (length mid - length suffix) line
          , prefix == prefix'
          , suffix == suffix' ]
        parse xs =
          let toks = scan (BSL.pack xs)
          in case run_ parser (UserState initialState toks) of
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
        lookup :: (Ord a, Hashable a) => Map BS.ByteString a -> BS.ByteString -> a
        lookup m x = Map.findWithDefault (error "runE: result from E mentions free names") x m