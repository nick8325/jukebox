{-# LANGUAGE GADTs #-}
module Provers.E where

import Form hiding (tag)
import Name
import Options
import Control.Applicative hiding (Const)
import Control.Monad
import Utils
import TPTP.Parsec
import TPTP.ClauseParser hiding (newFunction)
import TPTP.Print
import TPTP.Lexer hiding (Normal, keyword, Axiom)
import Text.PrettyPrint.HughesPJ
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL

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
mangleAnswer t = aux (typeRep t) t (unpack t)
  where aux TermRep (f :@: [t]) _
          | stringBaseName f == "$answer" = do
            wrap <- newFunction "answer" [typ t] (head (funArgs f))
            return (f :@: [wrap :@: [t]])
        aux _ t Const{} = return t
        aux _ _ (Unary f x) = fmap f (mangleAnswer x)
        aux _ _ (Binary f x y) = liftM2 f (mangleAnswer x) (mangleAnswer y)

runE :: (Pretty a, Symbolic a) => EFlags -> Problem a -> IO (Problem Form)
runE flags prob
  | not (isFof (open prob)) = error "runE: E doesn't support many-typed problems"
  | otherwise = do
    res <- popen (eprover flags) eflags
           (BS.pack (render (prettyProblem "fof" Normal (close prob mangleAnswer))))
    case res of
      Left code -> error $ "runE: E failed with exit code " ++ show code
      Right str -> return (parseResult str)
  where eflags = [ "--soft-cpu-limit=" ++ show n | Just n <- [timeout flags] ] ++
                 ["--memory-limit=" ++ show n | Just n <- [memory flags] ] ++
                 ["--tstp-in", "--tstp-out", "-tAuto", "-xAuto"]

parseResult :: BS.ByteString -> Problem Form
parseResult str = runParser (many p) str
  where runParser p str =
          case run_ p (UserState initialState (scan (findClauses (BSL.fromChunks [str])))) of
            Ok (UserState (MkState _ _ _ _ _ n) _) x ->
              close_ n (return x)
            _ -> error "runE: Couldn't parse returned clauses"
        findClauses = BSL.unlines . pick . BSL.lines
          where pick xs = [ BSL.drop 4 x | x <- xs, BSL.take 4 x == BSL.pack "#cnf" ]
        p = do
          punct LParen
          name <- tag
          punct Comma
          keyword Plain
          punct Comma
          clause <- cnf
          punct RParen
          punct Dot
          return (Input name Axiom clause)