-- A folly :)
{-# LANGUAGE GeneralizedNewtypeDeriving, BangPatterns #-}
module Progress where

import System.IO
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import Control.Monad
import Control.Monad.Trans.State.Strict hiding (State)
import TPTP

data State = State {-# UNPACK #-} !Int {-# UNPACK #-} !Int {-# UNPACK #-} !Int
newtype Progress m a = Progress (StateT State m a) deriving (Monad, MonadTrans, MonadIO, Functor)

{-# INLINE tick #-}
tick :: MonadIO m => Progress m ()
tick = Progress $ do
  State current freq pos <- get
  if current == 0
    then update freq pos
    else put (State (current-1) freq pos)

{-# NOINLINE update #-}
update :: MonadIO m => Int -> Int -> StateT State m ()
update freq pos = do
  let spinny 0 = ".-\08"
      spinny 1 = "\\\08"
      spinny 2 = "|\08"
      spinny 3 = "/\08"
  liftIO $ putStr (spinny pos) >> hFlush stdout
  put $ State (freq-1) freq ((pos+1) `mod` 4)

runProgress :: MonadIO m => Progress m a -> Int -> String -> m a
runProgress (Progress x) freq msg = do
  liftIO $ putStr msg >> hFlush stdout
  res <- evalStateT x (State (freq-1) freq 0)
  liftIO (putStrLn ".")
  return res
