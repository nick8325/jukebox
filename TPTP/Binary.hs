{-# LANGUAGE TypeOperators, TemplateHaskell, TypeSynonymInstances, FlexibleInstances, GeneralizedNewtypeDeriving #-}
module TPTP.Binary where

import Data.DeriveTH
import Data.Derive.BinaryShared
import Form
import Name
import NameMap
import Seq(Seq(..))
import BinaryShared hiding (encode, decode)
import qualified BinaryShared as B
import Control.Monad
import Control.Monad.Trans
import Data.Word
import Data.Typeable
import qualified Data.ByteString.Lazy as BSL
import Codec.Compression.GZip

$(derive makeBinaryShared ''DomainSize)
$(derive makeBinaryShared ''Form)
$(derive makeBinaryShared ''FunType)
$(derive makeBinaryShared ''Term)
$(derive makeBinaryShared ''Atomic)
$(derive makeBinaryShared ''Signed)
$(derive makeBinaryShared ''Connective)
$(derive makeBinaryShared ''Clause)
$(derive makeBinaryShared ''Kind)
$(derive makeBinaryShared ''Input)
$(derive makeBinaryShared ''Bind)
$(derive makeBinaryShared ''Seq)

instance Binary a => Binary (Closed a) where
  get = do
    i <- get
    x <- get
    return (unsafeClose i x)
  put x = do { put (maxIndex x); put (open x) }

instance Binary Type where
  get = getShared
  put = putShared
instance Binary (Unshared Type) where
  get = fmap Unshared $ do
    tag <- getWord8
    case tag of
      0 -> return O
      1 -> liftM4 Type get get get get
  put (Unshared x) = do
    case x of
      O -> putWord8 0
      Type a b c d -> do
        putWord8 1
        put a
        put b
        put c
        put d

instance Binary Name where
  get = getShared
  put = putShared
instance Binary (Unshared Name) where
  get = fmap Unshared (liftM2 unsafeMakeName get get)
  put (Unshared name) = do { put (uniqueId name); put (base name) }

instance (Named a, Typeable a, Typeable b) => Binary (a ::: b) where
  get = getShared
  put = putShared
instance (Named a, Typeable a, Typeable b, Binary a, Binary b) => Binary (Unshared (a ::: b)) where
  get = fmap Unshared (liftM2 (:::) get get)
  put (Unshared (x ::: y)) = do { put x; put y }

instance (Named a, Binary a) => Binary (NameMap a) where
  get = fmap fromList get
    where fromList :: Named a => [a] -> NameMap a
          fromList = NameMap.fromList
  put = put . NameMap.toList

data AllShared a = AllShared [Name] [Type] [Variable] [Function] a
instance Binary a => Binary (AllShared a) where
  get = do
    Shared ns (Shared tys (Shared vs (Shared fs x))) <- get
    return (AllShared ns tys vs fs x)
  put (AllShared ns tys vs fs x) =
    put (Shared ns (Shared tys (Shared vs (Shared fs x))))

encode :: (Binary a, Symbolic a) => Closed a -> BSL.ByteString
encode x = compress (B.encode (AllShared (names (open x)) (types (open x)) (vars (open x)) (functions (open x)) x))

decode :: (Binary a, Symbolic a) => BSL.ByteString -> Closed a
decode s =
  let AllShared _ _ _ _ x = B.decode (decompress s)
  in x