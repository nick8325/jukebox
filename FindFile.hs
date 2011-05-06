module FindFile where

import System.FilePath
import System.Directory
import System.Environment
import Control.Exception
import Prelude hiding (catch)

findFile :: [FilePath] -> FilePath -> IO (Maybe FilePath)
findFile [] file = return Nothing
findFile (path:paths) file = do
  let candidate = path </> file
  exists <- doesFileExist candidate
  if exists then return (Just candidate)
   else findFile paths file

findFileTPTP :: [FilePath] -> FilePath -> IO (Maybe FilePath)
findFileTPTP dirs file = do
  let f :: IOException -> IO [FilePath]
      f _ = return []
  tptp <- do { dir <- getEnv "TPTP"; return [dir] } `catch` f
  findFile (".":dirs++tptp) file
