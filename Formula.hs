{-# LANGUAGE TypeOperators #-}
module Formula where

import AppList(AppList)
import qualified AppList as A
import qualified Data.Set
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Hashable
import Data.HashMap(Map)
import qualified Data.HashMap as Map
import Data.Ord
import qualified Data.ByteString.Char8 as BS
import Data.List
import Utils
import Name

type Tag = BS.ByteString

data a ::: b = !a ::: !b

name :: (a ::: b) -> a
name (x ::: _) = x

instance Eq a => Eq (a ::: b) where s == t = name s == name t
instance Ord a => Ord (a ::: b) where compare = comparing name
instance Hashable a => Hashable (a ::: b) where hashWithSalt s = hashWithSalt s . name

instance Name a => Name (a ::: b) where
  baseName = baseName . name

data DomainSize = Finite !Int | Infinite deriving (Eq, Ord, Show)

data Type a =
    O
  | Type {
      tname :: !a,
      -- type is monotone when domain size is >= tmonotone
      tmonotone :: DomainSize,
      -- if there is a model of size >= tsize then there is a model of size tsize
      tsize :: DomainSize,
      -- two types in the same class have to have the same size
      tclass :: Int } deriving Show

instance Eq a => Eq (Type a) where
  t1 == t2 = tname t1 == tname t2

instance Ord a => Ord (Type a) where
  compare = comparing tname

instance Hashable a => Hashable (Type a) where
  hashWithSalt s = hashWithSalt s . tname

type Problem a b = Bind b (Bind (a ::: b) [Input (Formula (a ::: b))])

data Input a = Input
  { tag :: !Tag,
    kind :: !Kind,
    formula :: !a }

instance Functor Input where
  fmap f x = x { formula = f (formula x) }

data Term a = Var !a | !a :@: [Term a]
data Atom a = !(Term a) :=: !(Term a) | Tru !(Term a)
data Signed a = Signed { sign :: !Sign, value :: !a } deriving Show
data Sign = Pos | Neg deriving (Eq, Ord, Show)

instance Functor Signed where
  fmap f (Signed s x) = Signed s (f x)
type Literal a = Signed (Atom a)

data Formula a
  = Literal !(Literal a)
  | Not !(Formula a)
  | And !(AppList (Formula a))
  | Or !(AppList (Formula a))
  | Equiv !(Formula a) !(Formula a)
  | ForAll !(Bind a (Formula a))
  | Exists !(Bind a (Formula a))

neg :: Signed a -> Signed a
neg (Signed Pos x) = Signed Neg x
neg (Signed Neg x) = Signed Pos x

data Kind = Axiom | NegatedConjecture deriving (Eq, Ord)
