-- Strict lists with efficient append.
module AppList where

import Prelude hiding (concat)
import Control.Monad

data AppList a = Append !(AppList a) !(AppList a) | Unit !a | Nil

append :: AppList a -> AppList a -> AppList a
append Nil xs = xs
append xs Nil = xs
append xs ys = Append xs ys

instance Show a => Show (AppList a) where
  show = show . toList

cons :: a -> AppList a -> AppList a
cons x xs = Unit x `append` xs

snoc :: AppList a -> a -> AppList a
snoc xs x = xs `append` Unit x

instance Functor AppList where
  fmap f (Append x y) = Append (fmap f x) (fmap f y)
  fmap f (Unit x) = Unit (f x)
  fmap f Nil = Nil

instance Monad AppList where
  return = Unit
  x >>= f = concat (fmap f x)

instance MonadPlus AppList where
  mzero = Nil
  mplus = append

concat :: AppList (AppList a) -> AppList a
concat (Append x y) = concat x `append` concat y
concat (Unit x) = x
concat Nil = Nil

fold :: (b -> b -> b) -> (a -> b) -> b -> AppList a -> b
fold app u n (Append x y) = app (fold app u n x) (fold app u n y)
fold app u n (Unit x) = u x
fold app u n Nil = n

toList :: AppList a -> [a]
toList x = go [x]
  -- (if you squint here you can see difference lists...)
  where go (Nil:left) = go left
        go (Unit x:left) = x:go left
        go (Append x y:left) = go (x:y:left)
        go [] = []

fromList :: [a] -> AppList a
fromList = foldr cons Nil
