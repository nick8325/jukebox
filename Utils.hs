module Utils where

import Data.List

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
