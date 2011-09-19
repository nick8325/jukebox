module Utils where

import Data.List
import qualified Seq as Seq
import qualified Data.HashSet as Set
import Data.Hashable

usort :: Ord a => [a] -> [a]
usort = map head . group . sort

merge :: Ord a => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys) =
  case x `compare` y of
    LT -> x:merge xs (y:ys)
    EQ -> x:merge xs ys
    GT -> y:merge (x:xs) ys

nub :: (Seq.List f, Ord a, Hashable a) => f a -> [a]
nub = Set.toList . Set.fromList . Seq.toList