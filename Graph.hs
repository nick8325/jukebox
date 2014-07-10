{-# LANGUAGE TemplateHaskell #-}
module Jukebox.Graph where

import Data.Map as M
import Data.Set as S
import Data.Maybe
import Data.List

import Test.QuickCheck
import Test.QuickCheck.Poly
import Test.QuickCheck.All

type Graph a = Map a [a]

build :: Ord a => [(a,a)] -> Graph a
build xys = M.map S.toList (M.fromListWith S.union [ (x,S.singleton y) | (x,y) <- xys ])

build2 :: Ord a => [(a,a)] -> Graph a
build2 xys = build (xys ++ [ (y,x) | (x,y) <- xys ])

nodes :: Ord a => Graph a -> Set a
nodes g = S.fromList [ z | (x,ys) <- M.toList g, z <- x:ys ]

classes :: Ord a => Graph a -> [Set a]
classes g = gather S.empty xs
 where
  xs = S.toList (nodes g)

  gather seen []        = []
  gather seen (x:xs)
    | x `S.member` seen = gather seen xs
    | otherwise         = rs : gather (seen `S.union` rs) xs
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

path :: Ord a => Graph a -> a -> a -> Maybe [a]
path g x y = find S.empty [(x,[])] [] y
 where
  find seen [] [] y =
    Nothing
  
  find seen [] qs y =
    find seen (reverse qs) [] y
  
  find seen ((x,p):ps) qs y
    | x `S.member` seen = find seen ps qs y
    | x == y            = Just (reverse (x:p))
    | otherwise         = find (S.insert x seen) ps ([ (y,x:p) | Just ys <- [M.lookup x g], y <- ys ] ++ qs) y

-- testing

data Node = Node Int deriving ( Eq, Ord )
data GraphA = Graph (Graph Node) deriving ( Show )

instance Show Node where
  show (Node n) = show n

instance Arbitrary Node where
  arbitrary = Node `fmap` choose (1,30)

instance Arbitrary GraphA where
  arbitrary = (Graph . build2) `fmap` arbitrary
  shrink (Graph g) = [ Graph (build2 xs') | xs' <- shrink (edges g) ]
   where
    edges g = nub [ (x,y) | (x,ys) <- M.toList g, y <- ys, x <= y ]

prop_Complete (Graph g) =
  let cs = classes g
      ns = nodes g   in
    ns == S.unions cs

prop_BigEnough (Graph g) =
  let cs = classes g in
    all isJust [ path g x y | c <- cs, x <- S.toList c, y <- S.toList c ]

prop_SmallEnough (Graph g) =
  let cs = classes g in
    all isNothing [ path g x y | c1 <- cs, c2 <- cs, c1 < c2, x <- S.toList c1, y <- S.toList c2 ]

prop_PathIsPath (Graph g) =
  let cs = classes g in
    and [ isPath x y p | c <- cs, x <- S.toList c, y <- S.toList c, Just p <- [path g x y] ]
 where
  isPath x y xs = head xs == x && last xs == y && all isEdge (xs `zip` tail xs)
  
  isEdge (x,y) = case M.lookup x g of
                   Nothing -> False
                   Just ys -> y `elem` ys

testAll = $(quickCheckAll)
