{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module TPTP where

import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Class
import Control.Monad.IO.Class

newtype TPTP m a = TPTP (ReaderT (FilePath -> IO (Maybe BSL.ByteString)) m a) deriving (MonadTrans, MonadIO, Monad, Functor)

readTPTPFile :: MonadIO m => FilePath -> TPTP m (Maybe BSL.ByteString)
readTPTPFile name =
  TPTP $ do
    findFile <- ask
    liftIO (findFile name)

runTPTP :: TPTP m a -> (FilePath -> IO (Maybe BSL.ByteString)) -> m a
runTPTP (TPTP x) f = runReaderT x f
