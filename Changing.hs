-- Functions to help with modifying a data structure while not copying
-- the bits that haven't changed. Intended to be imported qualified.

{-# LANGUAGE Rank2Types #-}
module Changing where

newtype Changing a =
  Changing { unChanging :: forall b. (a -> b) -> b -> b }

{-# INLINE value #-}
value :: a -> Changing a -> a
value x (Changing k) = k id x

{-# INLINE changed #-}
changed :: a -> Changing a
changed x = Changing (\c _ -> c x)

{-# INLINE unchanged #-}
unchanged :: Changing a
unchanged = Changing (\_ u -> u)

instance Functor Changing where
  fmap f (Changing k) = Changing (\c -> k (c . f))

{-# INLINE lift2 #-}
lift2 :: (a -> b -> c) -> a -> Changing a -> b -> Changing b -> Changing c
lift2 f x (Changing kx) y (Changing ky) =
  Changing
    (\c u ->
      kx (\x' -> ky (c . f x') (c (f x' y)))
         (ky (c . f x) u))
