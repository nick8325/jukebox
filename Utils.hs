module Utils where

import Data.List
import qualified Seq as Seq
import qualified Data.HashSet as Set
import Data.Hashable
import System.Process
import qualified Data.ByteString.Char8 as BS
import System.IO
import System.Exit
import Control.Applicative

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

popen :: FilePath -> [String] -> BS.ByteString -> IO (Either Int BS.ByteString)
popen prog args inp = do
  (Just stdin, Just stdout, Nothing, pid) <-
    createProcess CreateProcess {
      cmdspec = RawCommand prog args,
      cwd = Nothing,
      env = Nothing,
      std_in = CreatePipe,
      std_out = CreatePipe,
      std_err = Inherit,
      close_fds = False
      }
  BS.hPutStr stdin inp
  hFlush stdin
  hClose stdin
  code <- waitForProcess pid
  (case code of
    ExitSuccess -> fmap Right (BS.hGetContents stdout)
    ExitFailure code -> return (Left code))
    <* hClose stdout