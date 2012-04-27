module Graph where

import Data.Map as M
import Data.Set as S

type Graph a = Map a [a]

build :: Ord a => [(a,a)] -> Graph a
build xys = M.fromListWith (++) [ (x,[y]) | (x,y) <- xys ]

build2 :: Ord a => [(a,a)] -> Graph a
build2 xys = build (xys ++ [ (y,x) | (x,y) <- xys ])

nodes :: Ord a => Graph a -> Set a
nodes g = S.fromList [ z | (x,ys) <- M.toList g, z <- x:ys ]

classes :: Ord a => Graph a -> [[a]]
classes g = gather S.empty xs
 where
  xs = S.toList (nodes g)

  gather seen []        = []
  gather seen (x:xs)
    | x `S.member` seen = gather seen xs
    | otherwise         = S.toList rs : gather (seen `S.union` rs) xs
   where
    rs = explore S.empty [x]
    
  explore seen [] = seen
  explore seen (x:xs)
    | x `S.member` seen = explore seen xs
    | otherwise         = explore (S.insert x seen) (ys ++ xs)
   where
    ys = case M.lookup x g of
           Nothing -> []
           Just ys -> ys

