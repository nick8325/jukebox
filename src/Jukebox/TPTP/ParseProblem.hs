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

    readInFile pos name = do
      mfile <- liftIO (findFile name)
      case mfile of
        Nothing ->
          err pos ("File '" ++ name ++ "' not found")
        Just file ->
          ExceptT $ do
            liftIO $ hPutStrLn stderr $ "Reading " ++ file ++ "..."
            fmap Right (readFile file) `catch`
              \(e :: IOException) -> return (Left (show e))

    process (Parser.ParseFailed loc msg) = err loc (intercalate "\n" msg)
    process (Parser.ParseSucceeded prob) = return prob
    process (Parser.ParseStalled loc name cont) = do
      file <- readInFile loc name
      process (cont file)
