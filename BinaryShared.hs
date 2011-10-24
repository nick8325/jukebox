{-# LANGUAGE ExistentialQuantification, GeneralizedNewtypeDeriving, TemplateHaskell #-}
module BinaryShared where

import qualified Data.Binary.Put as Put
import qualified Data.Binary.Get as Get
import qualified Data.Binary as Binary
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Reader
import Data.DeriveTH
import Data.Derive.Hashable
import Data.Derive.BinaryShared
import Data.Hashable
import qualified Map
import qualified Data.ByteString.Lazy as BSL
import qualified Data.ByteString as BS
import Data.Int
import Data.Word
import Data.Typeable
import Data.Maybe
import System.IO.Unsafe
import GHC.Prim(Any)
import Unsafe.Coerce

default ()

data Shared a b = Shared [a] b

newtype Put a = Put { runPut :: ReaderT (S Obj Id) Put.PutM a } deriving (Functor, Monad, MonadReader (S Obj Id))
newtype Get a = Get { runGet :: ReaderT (S Id Any) Get.Get a } deriving (Functor, Monad, MonadReader (S Id Any))
data Id = Id {-# UNPACK #-} !Word {-# UNPACK #-} !Word deriving (Eq, Ord)
data S a b = S {-# UNPACK #-} !Word !(Map.Map a b)

class Binary a where
  get :: Get a
  put :: a -> Put ()

class BinaryUnshared a where
  getUnshared :: Get a
  putUnshared :: a -> Put ()

liftGet :: Get.Get a -> Get a
liftGet = Get . lift

liftPut :: Put.PutM a -> Put a
liftPut = Put . lift

getWord8 :: Get Word8
getWord8 = liftGet Get.getWord8

putWord8 :: Word8 -> Put ()
putWord8 = liftPut . Put.putWord8

withObjs :: (Monad m, Typeable a, Hashable a, Ord a, Hashable b, Ord b) =>
            [a] -> (a -> Id -> (b, c)) ->
            ReaderT (S b c) m d ->
            ReaderT (S b c) m d
withObjs xs swap m = withReaderT f m
  where f (S lev map) = S (lev+1) (map `Map.union` map' lev)
        map' lev = Map.fromList [ swap x (Id lev n) | (n, x) <- zip [0..] xs ]

instance (BinaryUnshared a, Typeable a, Hashable a, Ord a, Binary b) => Binary (Shared a b) where
  get = do
    xs <- getList getUnshared
    x <- Get (withObjs xs (\x y -> (y, unsafeCoerce x)) (runGet get))
    return (Shared xs x)

  put (Shared xs x) = do
    putList putUnshared xs
    Put (withObjs xs (\x y -> (Obj x, y)) (runPut (put x)))

putShared :: (Typeable a, Ord a, Hashable a) => a -> Put ()
putShared x = do
  S _ map <- ask
  put (Map.findWithDefault (error "putShared: key not found") (Obj x) map)

getShared :: (Typeable a, Ord a, Hashable a) => Get a
getShared = do
  S _ map <- ask
  x <- get
  return $! unsafeCoerce (Map.findWithDefault (error "getShared: key not found") x map)

data Obj = forall a. (Typeable a, Ord a, Hashable a) => Obj a

objType :: Typeable a => a -> Int
objType = unsafePerformIO . typeRepKey . typeOf

instance Eq Obj where
  Obj x == Obj y =
    case cast x of
      Just x' -> x' == y
      Nothing -> False

instance Ord Obj where
  compare (Obj x) (Obj y) =
    case cast x of
      Just x' -> x' `compare` y
      Nothing -> objType x `compare` objType y

instance Hashable Obj where
  hashWithSalt s (Obj x) = s `hashWithSalt` objType x `hashWithSalt` x 

encode :: Binary a => a -> BSL.ByteString
encode x = Put.runPut (runReaderT (runPut (put x)) (S 0 Map.empty))

decode :: Binary a => BSL.ByteString -> a
decode = Get.runGet (runReaderT (runGet get) (S 0 Map.empty))

getIntegral :: (Binary.Binary a, Integral a) => Get a
getIntegral = do
  n <- getWord8
  if n == 255 then liftGet Binary.get else return $! fromIntegral n

putIntegral :: (Binary.Binary a, Integral a) => a -> Put ()
putIntegral x
  | x >= 0 && x < 255 = putWord8 (fromIntegral x)
  | otherwise = do
    putWord8 255
    liftPut (Binary.put x)

instance Binary Int where
  get = getIntegral
  put = putIntegral

instance Binary Integer where
  get = getIntegral
  put = putIntegral

instance Binary Int64 where
  get = getIntegral
  put = putIntegral

instance Binary Word8 where
  get = getIntegral
  put = putIntegral

instance Binary Word32 where
  get = getIntegral
  put = putIntegral

instance Binary Word where
  get = getIntegral
  put = putIntegral

instance Binary a => Binary [a] where
  get = getList get
  put = putList put

getList get_ = do
  len <- get :: Get Int
  replicateM len get_

putList put_ xs = do
    put (length xs :: Int)
    mapM_ put_ xs

instance Binary BS.ByteString where
  get = do
    len <- get :: Get Int
    liftGet (Get.getByteString len)
  put x = do
    put (BS.length x :: Int)
    liftPut (Put.putByteString x)

$(derive makeHashable ''Id)
$(derive makeBinaryShared ''Id)