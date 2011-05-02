module TPTP where

import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL

data TPTP a = ReadFile BS.ByteString (Maybe BSL.ByteString -> TPTP a)
            | Done a

instance Monad TPTP where
  return = Done
  ReadFile file cont >>= f = ReadFile file ((>>= f) . cont)
  Done x >>= f = f x
