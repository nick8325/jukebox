{-# LANGUAGE TypeOperators, GeneralizedNewtypeDeriving, FlexibleInstances, DeriveDataTypeable #-}
module Name(
  Name, uniqueId, base,
  unsafeMakeName,
  (:::)(..), lhs, rhs,
  Named(..),
  Closed, close, close_, open, closed0, stdNames, nameO, nameI, NameM, newName,
  unsafeClose, maxIndex,
  uniquify) where

import qualified Data.ByteString.Char8 as BS
import Data.Hashable
import qualified Data.HashMap as Map
import Utils
import Data.List
import Data.Ord
import Data.Int
import Data.Typeable
import Control.Monad.State.Strict

data Name =
  Name {
    uniqueId :: {-# UNPACK #-} !Int64,
    base :: BS.ByteString } deriving Typeable

unsafeMakeName = Name

instance Eq Name where
  x == y = uniqueId x == uniqueId y

instance Ord Name where
  compare = comparing uniqueId

instance Hashable Name where
  hashWithSalt s = hashWithSalt s . uniqueId

instance Show Name where
  show Name { uniqueId = uniqueId, base = base } =
    BS.unpack base ++ show uniqueId

class Named a where
  name :: a -> Name
  baseName :: a -> BS.ByteString
  baseName = base . name

instance Named BS.ByteString where
  name = error "Name.name: used a ByteString as a name"
  baseName = id

instance Named [Char] where
  name = error "Name.name: used a String as a name"
  baseName = BS.pack

instance Named Name where
  name = id

data a ::: b = !a ::: !b deriving (Show, Typeable)

lhs :: (a ::: b) -> a
lhs (x ::: _) = x

rhs :: (a ::: b) -> b
rhs (_ ::: y) = y

instance Named a => Eq (a ::: b) where s == t = name s == name t
instance Named a => Ord (a ::: b) where compare = comparing name
instance Named a => Hashable (a ::: b) where hashWithSalt s = hashWithSalt s . name

instance Named a => Named (a ::: b) where
  name (a ::: b) = name a

newtype NameM a =
  NameM { unNameM :: State Int64 a }
    deriving (Functor, Monad)

newName :: Named a => a -> NameM Name
newName x = NameM $ do
  idx <- get
  let idx'= idx+1
  when (idx' < 0) $ error "Name.newName: too many names"
  put $! idx'
  return $! Name idx' (baseName x)

data Closed a =
  Closed {
    maxIndex :: {-# UNPACK #-} !Int64,
    open :: !a } deriving Typeable

unsafeClose = Closed

instance Functor Closed where
  fmap f (Closed m x) = Closed m (f x)

closed0 :: Closed ()
nameO, nameI :: Name

closed0 = close_ stdNames (return ())
[nameO, nameI] = open stdNames

stdNames :: Closed [Name]
stdNames = close (Closed 0 ["$o", "$i"]) (mapM newName)

close :: Closed a -> (a -> NameM b) -> Closed b
close Closed{ maxIndex = maxIndex, open = open } f =
  let (open', maxIndex') = runState (unNameM (f open)) maxIndex
  in Closed{ maxIndex = maxIndex', open = open' }

close_ :: Closed a -> NameM b -> Closed b
close_ x m = close x (const m)

uniquify :: [Name] -> (Name -> BS.ByteString)
uniquify xs = f
  -- Note to self: nameO should always be mapped to "$o".
  -- Therefore we make sure that smaller names have priority
  -- over bigger names here.
  where
    baseMap =
      -- Assign numbers to each baseName
      Map.map (\xs -> Map.fromList (zip (usort xs) [0 :: Int ..])) .
      -- Partition by baseName
      foldl' (\m x -> Map.insertWith (++) (base x) [x] m) Map.empty $
      xs
    f x = combine (base x) b
      where
        b = Map.findWithDefault (error "Name.uniquify: name not found") x
            (Map.findWithDefault (error "Name.uniquify: name not found") (baseName x) baseMap)
    combine s 0 = s
    combine s n = disambiguate (BS.append s (BS.pack (show n)))
    disambiguate s
      | not (Map.member s baseMap) = s
      | otherwise =
        -- Odd situation: we have e.g. a name with baseName "f1",
        -- and two names with baseName "f", which would normally
        -- become "f" and "f1", but the "f1" conflicts.
        -- Try appending some suffix.
        disambiguate (BS.snoc s '_')
