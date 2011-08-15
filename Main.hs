{-# LANGUAGE ImplicitParams #-}
module Main where

import TPTP.ParseProblem
import System.Environment
import Formula
-- import InferTypes
import TPTP.Print
import Name
import Text.PrettyPrint.HughesPJ

main = do
  [arg] <- getArgs
  res <- parseProblem arg
  case res of
    Left err -> putStrLn err
    Right p -> do
      -- let ?monotone = const Infinite
      --     ?size = const Infinite
      -- in putStrLn (prettyShow (infer p))
      putStrLn $ "ok, " ++ show (length (open p)) ++ " clauses"
      putStrLn (render (prettyProblem "tff" Chatty p))
      putStrLn (render (prettyProblem "tff" Normal p))
