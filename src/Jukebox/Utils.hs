{-# LANGUAGE TupleSections #-}
module Jukebox.Utils where

import System.Process
import System.IO
import System.Exit
import Control.Concurrent
import qualified Data.Set as Set

usort :: Ord a => [a] -> [a]
--usort = map head . group . sort
usort = Set.toAscList . Set.fromList

merge :: Ord a => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys) =
  case x `compare` y of
    LT -> x:merge xs (y:ys)
    EQ -> x:merge xs ys
    GT -> y:merge (x:xs) ys

popen :: FilePath -> [String] -> String -> IO (ExitCode, String)
popen prog args inp = do
  (stdin, stdout, stderr_, pid) <- runInteractiveProcess prog args Nothing Nothing
  forkIO $ hGetContents stderr_ >>= hPutStr stderr
  hPutStr stdin inp
  hFlush stdin
  hClose stdin
  code <- waitForProcess pid
  fmap (code,) (hGetContents stdout) <* hClose stdout
