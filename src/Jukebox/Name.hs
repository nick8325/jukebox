{-# LANGUAGE TypeOperators, GeneralizedNewtypeDeriving, FlexibleInstances #-}
module Jukebox.Name where

import Control.Monad
import Control.Monad.Trans.State.Strict
import qualified Data.Map.Strict as Map
import Data.List
import Data.Ord
import Jukebox.Utils
import Data.Int
import Data.Symbol

data Name =
    Fixed {-# UNPACK #-} !Symbol
  | Unique {-# UNPACK #-} !Int64 String

base :: Named a => a -> String
base x =
  case name x of
    Fixed xs -> unintern xs
    Unique _ xs -> xs

instance Eq Name where
  x == y = compareName x == compareName y

instance Ord Name where
  compare = comparing compareName

compareName :: Name -> Either Symbol Int64
compareName (Fixed xs) = Left xs
compareName (Unique n _) = Right n

instance Show Name where
  show (Fixed xs) = unintern xs
  show (Unique n xs) = xs ++ "@" ++ show n

class Named a where
  name :: a -> Name

instance Named [Char] where
  name = Fixed . intern

instance Named Name where
  name = id

data a ::: b = a ::: b deriving Show

lhs :: (a ::: b) -> a
lhs (x ::: _) = x

rhs :: (a ::: b) -> b
rhs (_ ::: y) = y

instance Named a => Eq (a ::: b) where s == t = name s == name t
instance Named a => Ord (a ::: b) where compare = comparing name

instance Named a => Named (a ::: b) where
  name (a ::: b) = name a

newtype NameM a =
  NameM { unNameM :: State Int64 a }
    deriving (Functor, Applicative, Monad)

runNameM :: [Name] -> NameM a -> a
runNameM xs m =
  evalState (unNameM m) (maximum (0:[ succ n | Unique n _ <- xs ]))

newName :: Named a => a -> NameM Name
newName x = NameM $ do
  idx <- get
  let idx' = idx+1
  when (idx' < 0) $ error "Name.newName: too many names"
  put $! idx'
  return $! Unique idx' (base x)
