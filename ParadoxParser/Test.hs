{-# LANGUAGE BangPatterns #-}
module ParadoxParser.Test where

import Control.Monad
import TPTP.ParseProblem
import ParadoxParser.Convert
import ParadoxParser.ParseProblem
import Name

testParserIO :: [FilePath] -> Bool -> FilePath -> IO ()
testParserIO dirs verbose file = do
  !new <- parseProblem dirs file
  !old <- readProblemWithRoots dirs file
  let new' =
        case new of
          Left err -> error err
          Right ok -> map input (open ok)
  if old == new'
     then putStrLn "OK"
     else do
       putStrLn "Bad"
       when verbose $ do
         putStr "Old parser: "
         print old
         putStrLn ""
         putStr "New parser: "
         print new'
         putStrLn ""