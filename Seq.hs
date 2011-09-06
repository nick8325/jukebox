-- Strict lists with efficient append.
module Seq where

import Prelude hiding (concat, concatMap, length, mapM)
import Control.Monad hiding (mapM)
import Data.Hashable
import qualified Data.HashSet as Set

data Seq a = Append (Seq a) (Seq a) | Unit a | Nil

class List f where
  fromList :: f a -> Seq a
  toList :: f a -> [a]

instance List [] where
  fromList = foldr cons Nil
  toList = id

instance List Seq where
  fromList = id
  toList x = go [x]
    -- (if you squint here you can see difference lists...)
    where go (Nil:left) = go left
          go (Unit x:left) = x:go left
          go (Append x y:left) = go (x:y:left)
          go [] = []

appendA :: Seq a -> Seq a -> Seq a
appendA Nil xs = xs
appendA xs Nil = xs
appendA xs ys = Append xs ys

instance Show a => Show (Seq a) where
  show = show . toList

cons :: a -> Seq a -> Seq a
cons x xs = Unit x `appendA` xs

snoc :: Seq a -> a -> Seq a
snoc xs x = xs `appendA` Unit x

append :: (List f, List g) => f a -> g a -> Seq a
append xs ys = fromList xs `appendA` fromList ys

instance Functor Seq where
  fmap f (Append x y) = Append (fmap f x) (fmap f y)
  fmap f (Unit x) = Unit (f x)
  fmap f Nil = Nil

instance Monad Seq where
  return = Unit
  x >>= f = concatMapA f x
  fail _ = Nil

instance MonadPlus Seq where
  mzero = Nil
  mplus = append

concat :: (List f, List g) => f (g a) -> Seq a
concat = concatMap id

concatMap :: (List f, List g) => (a -> g b) -> f a -> Seq b
concatMap f xs = concatMapA (fromList . f) (fromList xs)

concatMapA :: (a -> Seq b) -> Seq a -> Seq b
concatMapA f = aux
  where aux (Append x y) = aux x `appendA` aux y
        aux (Unit x) = f x
        aux Nil = Nil

fold :: (b -> b -> b) -> (a -> b) -> b -> Seq a -> b
fold app u n (Append x y) = app (fold app u n x) (fold app u n y)
fold app u n (Unit x) = u x
fold app u n Nil = n

unique :: (Ord a, Hashable a, List f) => f a -> [a]
unique = Set.toList . Set.fromList . toList . fromList

length :: Seq a -> Int
length Nil = 0
length (Unit _) = 1
length (Append x y) = length x + length y

mapM :: Monad m => (a -> m b) -> Seq a -> m (Seq b)
mapM f Nil = return Nil
mapM f (Unit x) = liftM Unit (f x)
mapM f (Append x y) = liftM2 Append (mapM f x) (mapM f y)
