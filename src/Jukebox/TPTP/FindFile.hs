{-# LANGUAGE CPP #-}
module Jukebox.TPTP.FindFile where

import System.FilePath
import System.Directory(doesFileExist)
import System.Environment
import Control.Exception
import Control.Monad
import Jukebox.Options
#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
import Data.Traversable(sequenceA)
#endif

findFile :: [FilePath] -> FilePath -> IO (Maybe FilePath)
findFile [] _file = return Nothing
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
