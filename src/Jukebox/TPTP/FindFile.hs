module Jukebox.TPTP.FindFile where

import System.FilePath
import System.Directory(doesFileExist)
import System.Environment
import Control.Applicative
import Control.Exception
import Control.Monad
import Prelude hiding (catch)
import Jukebox.Options
import Data.Traversable(sequenceA)

findFile :: [FilePath] -> FilePath -> IO (Maybe FilePath)
findFile [] file = return Nothing
findFile (path:paths) file = do
  let candidate = path </> file
  exists <- doesFileExist candidate
  if exists then return (Just candidate)
   else findFile paths file

findFileTPTP :: [FilePath] -> FilePath -> IO (Maybe FilePath)
findFileTPTP dirs file = do
  let candidates = [file, "Problems" </> file,
                    "Problems" </> take 3 file </> file]
  fmap msum (mapM (findFile dirs) candidates)

getTPTPDirs :: IO [FilePath]
getTPTPDirs = do { dir <- getEnv "TPTP"; return [dir] } `catch` f
  where f :: IOException -> IO [FilePath]
        f _ = return []

findFileFlags =
  concat <$>
  sequenceA [
    pure ["."],
    flag "root"
      ["Extra directories that will be searched for TPTP input files."]
      []
      argFiles,
    io getTPTPDirs
    ]
