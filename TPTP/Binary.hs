{-# LANGUAGE TypeOperators, TypeSynonymInstances, FlexibleInstances, GeneralizedNewtypeDeriving #-}
module TPTP.Binary where

import Data.DeriveTH
import Data.Derive.BinaryShared
import Data.Derive.BinaryUnshared
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
$(derive makeBinaryUnshared ''Type)
$(derive makeBinaryUnshared ''(:::))

instance Binary Type where
  get = getShared
  put = putShared

instance Binary Name where
  get = getShared
  put = putShared

instance BinaryUnshared Name where
  getUnshared = liftM2 unsafeMakeName get get
  putUnshared name = do { put (uniqueId name); put (base name) }

instance (Named a, Typeable a, Typeable b) => Binary (a ::: b) where
  get = getShared
  put = putShared

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

instance (Symbolic a, Binary a) => Binary (Closed a) where
  get = do
    i <- get
    AllShared _ _ _ _ x <- get
    return (unsafeClose i x)
  put x = do
    put (maxIndex x)
    let x' = open x
    put (AllShared (names x') (types x') (vars x') (functions x') x')

encode :: (Binary a, Symbolic a) => Closed a -> BSL.ByteString
encode x = B.encode x

decode :: (Binary a, Symbolic a) => BSL.ByteString -> Closed a
decode s = B.decode s
