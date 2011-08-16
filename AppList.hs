-- Strict lists with efficient append.
module AppList where

import Prelude hiding (concat)
import Control.Monad
import Data.Hashable
import qualified Data.HashSet as Set

data AppList a = Append !(AppList a) !(AppList a) | Unit !a | Nil

class List f where
  fromList :: f a -> AppList a
  toList :: f a -> [a]

instance List [] where
  fromList = foldr cons Nil
  toList = id

instance List AppList where
  fromList = id
  toList x = go [x]
    -- (if you squint here you can see difference lists...)
    where go (Nil:left) = go left
          go (Unit x:left) = x:go left
          go (Append x y:left) = go (x:y:left)
          go [] = []

appendA :: AppList a -> AppList a -> AppList a
appendA Nil xs = xs
appendA xs Nil = xs
appendA xs ys = Append xs ys

instance Show a => Show (AppList a) where
  show = show . toList

cons :: a -> AppList a -> AppList a
cons x xs = Unit x `appendA` xs

snoc :: AppList a -> a -> AppList a
snoc xs x = xs `appendA` Unit x

append :: (List f, List g) => f a -> g a -> AppList a
append xs ys = fromList xs `appendA` fromList ys

instance Functor AppList where
  fmap f (Append x y) = Append (fmap f x) (fmap f y)
  fmap f (Unit x) = Unit (f x)
  fmap f Nil = Nil

instance Monad AppList where
  return = Unit
  x >>= f = concatA (fmap f x)
  fail _ = Nil

instance MonadPlus AppList where
  mzero = Nil
  mplus = append

concat :: (List f, List g) => f (g a) -> AppList a
concat xs = concatA (fmap fromList (fromList xs))

concatA :: AppList (AppList a) -> AppList a
concatA (Append x y) = concatA x `appendA` concatA y
concatA (Unit x) = x
concatA Nil = Nil

fold :: (b -> b -> b) -> (a -> b) -> b -> AppList a -> b
fold app u n (Append x y) = app (fold app u n x) (fold app u n y)
fold app u n (Unit x) = u x
fold app u n Nil = n

unique :: (Ord a, Hashable a, List f) => f a -> [a]
unique = Set.toList . Set.fromList . toList . fromList
