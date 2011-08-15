{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Name(
  Name, uniqueId,
  Named(name),
  Closed, close, open, NameM, newName,
  uniquify) where

import qualified Data.ByteString.Char8 as BS
import Data.Hashable
import qualified Data.HashMap as Map
import Utils
import Data.List
import Data.Ord
import Data.Int
import Control.Monad.State

data Name =
  Name {
    uniqueId :: {-# UNPACK #-} !Int64,
    base :: BS.ByteString }

instance Eq Name where
  x == y = name x == name y

instance Ord Name where
  compare = comparing name

instance Hashable Name where
  hashWithSalt s = hashWithSalt s . name

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

instance Named Name where
  name = id

newtype NameM a =
  NameM { unNameM :: State Int64 a }
    deriving (Functor, Monad)

newName :: Named a => a -> NameM Name
newName x = NameM $ do
  idx <- get
  let idx'= idx+1
  when (idx' < 0) $ error "Name.newName: too many names"
  put idx'
  return (Name idx' (baseName x))

data Closed a =
  Closed {
    maxIndex :: !Int64,
    open :: !a }

close :: Closed a -> (a -> NameM b) -> Closed b
close Closed{ maxIndex = maxIndex, open = open } f =
  case runState (unNameM (f open)) maxIndex of
    (open', maxIndex') ->
      Closed{ maxIndex = maxIndex', open = open' }

uniquify :: [Name] -> (Name -> BS.ByteString)
uniquify xs = f
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
    combine s n = disambiguate (BS.append s (BS.pack ('_':show n)))
    disambiguate s
      | not (Map.member s baseMap) = s
      | otherwise =
        -- Odd situation: we have e.g. a name with baseName "f_1",
        -- and two names with baseName "f", which would normally
        -- become "f" and "f_1", but the "f_1" conflicts.
        -- Try appending some suffix.
        disambiguate (BS.snoc s 'a')
