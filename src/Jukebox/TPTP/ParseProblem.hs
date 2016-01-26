{-# LANGUAGE ScopedTypeVariables #-}
module Jukebox.TPTP.ParseProblem where

import Jukebox.TPTP.FindFile
import qualified Jukebox.TPTP.ClauseParser as Parser
import Jukebox.TPTP.Lexer hiding (Include, Error)
import Jukebox.TPTP.Parsec
import Jukebox.TPTP.Print
import qualified Jukebox.TPTP.Lexer as L
import Control.Monad.IO.Class
import Control.Monad.Trans.Except
import Jukebox.Form hiding (Pos, run)
import Control.Monad.Trans.Identity
import Control.Exception
import Prelude hiding (catch)
import Data.List
import Jukebox.Name
import System.IO

parseProblem :: [FilePath] -> FilePath -> IO (Either String (Problem Form))
parseProblem dirs name = parseProblemWith (findFileTPTP dirs) name

parseProblemWith :: (FilePath -> IO (Maybe FilePath)) -> FilePath -> IO (Either String (Problem Form))
parseProblemWith findFile name =
  runExceptT $ do
    file <- readInFile "<command line>" (Pos 0 0) name
    process (Parser.parseProblem name file)

  where
    err file (Pos l c) msg = throwE msg'
      where
        msg' = "Error at " ++ file ++ " (line " ++ show l ++ ", column " ++ show c ++ "):\n" ++ msg

    readInFile parent pos name = do
      mfile <- liftIO (findFile name)
      case mfile of
        Nothing ->
          err parent pos ("File '" ++ name ++ "' not found")
        Just file ->
          ExceptT $ do
            liftIO $ hPutStrLn stderr $ "Reading " ++ file ++ "..."
            fmap Right (readFile file) `catch`
              \(e :: IOException) -> return (Left (show e))

    process (Parser.ParseFailed name pos msg) = err name pos (intercalate "\n" msg)
    process (Parser.ParseSucceeded prob) = return prob
    process (Parser.ParseStalled parent pos name cont) = do
      file <- readInFile parent pos name
      process (cont file)
