{-# LANGUAGE ScopedTypeVariables #-}
module Jukebox.TPTP.Parse where

import Jukebox.TPTP.FindFile
import qualified Jukebox.TPTP.Parse.Core as Parser
import Control.Monad.IO.Class
import Control.Monad.Trans.Except
import Jukebox.Form hiding (Pos, run)
import Control.Exception
import Data.List

parseString :: String -> IO (Problem Form)
parseString xs =
  case Parser.parseProblem "<string>" xs of
    Parser.ParseFailed loc msg ->
      error ("Parse error at " ++ show loc ++ ":\n" ++ unlines msg)
    Parser.ParseSucceeded prob ->
      return prob
    Parser.ParseStalled loc _ _ ->
      error ("Include directive found at " ++ show loc)

parseProblem :: [FilePath] -> FilePath -> IO (Either String (Problem Form))
parseProblem dirs name = parseProblemWith (findFileTPTP dirs) name

parseProblemWith :: (FilePath -> IO (Maybe FilePath)) -> FilePath -> IO (Either String (Problem Form))
parseProblemWith findFile name =
  runExceptT $ do
    file <- readInFile (Parser.Location "<command line>" 0 0) name
    process (Parser.parseProblem name file)

  where
    err loc msg = throwE msg'
      where
        msg' = "Error in " ++ show loc ++ ":\n" ++ msg

    readInFile _ "-" =
      ExceptT $ do
        fmap Right getContents `catch`
          \(e :: IOException) -> return (Left (show e))
    readInFile pos name = do
      mfile <- liftIO (findFile name)
      case mfile of
        Nothing ->
          err pos ("File '" ++ name ++ "' not found")
        Just file ->
          ExceptT $ do
            fmap Right (readFile file) `catch`
              \(e :: IOException) -> return (Left (show e))

    process (Parser.ParseFailed loc msg) = err loc (intercalate "\n" msg)
    process (Parser.ParseSucceeded prob) = return prob
    process (Parser.ParseStalled loc name cont) = do
      file <- readInFile loc name
      process (cont file)
