{-# LANGUAGE ImplicitParams #-}
module Main where

import TPTP.ParseProblem
import System.Environment
import Formula
import InferTypes
import TPTP.Print

main = do
  [arg] <- getArgs
  res <- parseProblem arg
  case res of
    Left err -> putStrLn err
    Right p ->
      let ?monotone = const Infinite
          ?size = const Infinite
      in putStrLn (prettyShow (infer p))
-- putStrLn $ "ok, " ++ show (length (inputs p)) ++ " clauses"
