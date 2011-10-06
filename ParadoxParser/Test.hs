module ParadoxParser.Test where

import TPTP.ParseProblem
import ParadoxParser.Convert
import ParadoxParser.ParseProblem
import Name

testParserIO :: [FilePath] -> FilePath -> IO ()
testParserIO dirs file = do
  Right new <- parseProblem dirs file
  old <- readProblemWithRoots dirs file
  let new' = map input (open new)
  if old == new'
     then putStrLn "OK"
     else putStrLn "Bad"