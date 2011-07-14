-- Names and binding.

module Name where

import qualified Data.ByteString.Char8 as BS
import Data.HashMap(Map)
import qualified Data.HashMap as Map

-- Attempt 1: parametrise formulae on names.
-- Problem with this is: we need to do flattening, which is nasty.
-- So: allow generating a memo-function a -> Name for appropriate type a,
-- which does knot-tying by looking at the set of names in the final formula.

-- (But...I don't know...we would like to be able to keep existing names where possible...)

class Names a where
  names :: Applicative f => (forall a. Name a -> f (Name a)) -> a -> f a

withNames :: (Names a, Named b) => ((b -> Name) -> a) -> a

data Name = Name { base :: BS.ByteString, id :: {-# UNPACK #-} !Int }
data Named a = {-# UNPACK #-} !Name ::: !a
data Bind a b = Bind { names :: !(Map Name a), contents :: !b }

bind :: Map Name a -> ((Name -> a) -> b) -> Bind a b

instance Functor Bind where
  fmap f (Bind names contents) = Bind names (f contents)

instance Monad Bind where
  return x = Bind Map.empty x
  x >>= f = join (fmap f x)
    where join (Bind names (Bind names' contents)) =
            Bind (Map.unionWith (error "Bind: same name bound twice") names names')
                 contents

bind :: BS.ByteString -> c -> (
