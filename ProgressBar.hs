module ProgressBar(ProgressBar(..), tickOnRead, withProgressBar) where

import System.IO
import Data.IORef
import Data.Word
import qualified Data.ByteString.Lazy as BSL
--import Data.ByteString.Lazy.Progress
import Control.Exception
import Control.Monad
import Prelude hiding (last)

data ProgressBar = ProgressBar { 
  tick :: IO (),
  enter :: String -> IO (),
  leave :: IO ()
  }

data State = State {
  position :: Int,
  enabled :: Bool,
  level :: Int,
  last :: Last
  }
             
-- What happened last.
data Last = Tick | Enter | Leave

tickOnRead :: ProgressBar -> BSL.ByteString -> IO BSL.ByteString
tickOnRead p s = do
  let chunkSize = 1000000 :: Word64
  nextRef <- newIORef chunkSize
  let f _ index = do
        next <- readIORef nextRef
        when (next <= index) $ do
          tick p
          writeIORef nextRef (next + chunkSize)
  -- trackProgress f s
  return s

withProgressBar :: (ProgressBar -> IO a) -> IO a
withProgressBar f = do
  state <- newIORef State { position = 0, enabled = True, level = 0, last = Enter }
  let spinny 0 = ".-\08"
      spinny 1 = "\\\08"
      spinny 2 = "|\08"
      spinny 3 = "/\08"
      put s = hPutStr stderr s >> hFlush stderr
      tick = do
        s <- readIORef state
        pos <-
          case last s of
            Tick -> return (position s)
            Enter -> return 0
            Leave -> put " " >> return 0
        put (spinny pos)
        writeIORef state s{ position = (pos+1) `mod` 4, last = Tick }
      enter msg = do
        s <- readIORef state
        when (level s /= 0) (put " (")
        put (msg ++ "...")
        writeIORef state s{ last = Enter, level = level s + 1 }
      leave = do
        s <- readIORef state
        when (level s /= 1) (put ")")
        writeIORef state s{last = Leave, level = level s - 1 }
  f ProgressBar { tick = tick, enter = enter, leave = leave }
    `finally` put " \n"
