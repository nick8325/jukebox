module TPTP.ParseProblem where

import Text.Parsec(ParseError)

import ReadProblem.Driver
import ReadProblem.Parser
import ProgressBar
import FindFile

readProblem :: FilePath -> IO (Either ParseError (Problem Formula))
readProblem prob = withProgressBar $ \pb -> readProblemWith (findFileTPTP []) pb prob
  where f =

readProblemWith :: (FilePath -> IO (Maybe FilePath)) ->
                    ProgressBar -> FilePath -> IO (Either ParseError (Problem Formula))
readProblemWith = undefined

-- plan:
-- main parser produces lazy list of clauses---each clause is include specification or prolog-term or parse error.
-- include-thingy is an IO-monadic transformer of such lazy lists of clauses (this won't work or at least we need unsafeinterleaveio)
