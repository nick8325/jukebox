{-# LANGUAGE ImplicitParams #-}
module Main where

import TPTP.ParseProblem
import System.Environment
import Form
-- import InferTypes
import TPTP.Print
import Name
import Text.PrettyPrint.HughesPJ
import Clausify
import Flags
import qualified Data.ByteString.Char8 as BS
import Control.Monad
import Monotonicity

main = do
  args <- getArgs
  fl <- getFlags Equinox
  forM args $ \arg -> do
    res <- parseProblem arg
    case res of
      Left err -> putStrLn err
      Right p -> do
        -- let ?monotone = const Infinite
        --     ?size = const Infinite
        -- in putStrLn (prettyShow (infer p))
        putStrLn $ "ok, " ++ show (length (open p)) ++ " clauses"
        let ?flags = fl
        let cs = close (clausify p) (\(cs, _) -> return [ Input (BS.pack "foo") Axiom c | c <- cs ])
        putStrLn $ "ok, " ++ show (length (open cs)) ++ "clauses"
        -- putStrLn (render (prettyProblem "tff" Normal p))
        -- putStrLn (render (prettyProblem "tff" Normal cs))
        -- putStrLn (render (prettyProblem "tff" Chatty p))
        -- putStrLn (render (prettyProblem "tff" Chatty cs))
