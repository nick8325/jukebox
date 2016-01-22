{-# LANGUAGE TupleSections #-}
module Jukebox.Utils where

import Data.List
import qualified Jukebox.Seq as Seq
import qualified Data.HashSet as Set
import Data.Hashable
import System.Process
import System.IO
import System.Exit
import Control.Applicative
import Control.Concurrent

usort :: Ord a => [a] -> [a]
usort = map head . group . sort

merge :: Ord a => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys) =
  case x `compare` y of
    LT -> x:merge xs (y:ys)
    EQ -> x:merge xs ys
    GT -> y:merge (x:xs) ys

nub :: (Seq.List f, Ord a, Hashable a) => f a -> [a]
nub = Set.toList . Set.fromList . Seq.toList

popen :: FilePath -> [String] -> String -> IO (ExitCode, String)
popen prog args inp = do
  (stdin, stdout, stderr_, pid) <- runInteractiveProcess prog args Nothing Nothing
  forkIO $ hGetContents stderr_ >>= hPutStr stderr
  hPutStr stdin inp
  hFlush stdin
  hClose stdin
  code <- waitForProcess pid
  fmap (code,) (hGetContents stdout) <* hClose stdout
