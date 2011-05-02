-- A folly :)
module Progress where

import System.IO
import Control.Monad.IO.Class

data ProgressT m a = Tick (ProgressT m a) | Done a | Monadic (m (ProgressT m a))

progress :: MonadIO m => String -> ProgressT m a -> m a
progress msg x = liftIO (putStr msg) >> go 0 x
  where go n x = do
          liftIO $ putStr (spinny n) >> hFlush stdout
          case x of
            Tick x -> go ((n+1) `mod` 4) x
            Done x -> liftIO (putStrLn ".") >> return x
            Monadic x -> x >>= go n
        spinny 0 = ".-\08"
        spinny 1 = "\\\08"
        spinny 2 = "|\08"
        spinny 3 = "/\08"

silent :: Monad m => ProgressT m a -> m a
silent (Tick x) = silent x
silent (Done x) = return x
silent (Monadic x) = x >>= silent
