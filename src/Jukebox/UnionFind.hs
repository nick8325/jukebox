module Jukebox.UnionFind(UF, Replacement((:>)), (=:=), rep, evalUF, execUF, runUF, S, isRep, initial, reps) where

import Prelude hiding (min)
import Control.Monad
import Control.Monad.Trans.State.Strict
import Data.Map.Strict(Map)
import qualified Data.Map as Map

type S a = Map a a
type UF a = State (S a)
data Replacement a = a :> a

runUF :: S a -> UF a b -> (b, S a)
runUF s m = runState m s

evalUF :: S a -> UF a b -> b
evalUF s m = fst (runUF s m)

execUF :: S a -> UF a b -> S a
execUF s m = snd (runUF s m)

initial :: S a
initial = Map.empty

(=:=) :: Ord a => a -> a -> UF a (Maybe (Replacement a))
s =:= t | s == t = return Nothing
s =:= t = do
  rs <- rep s
  rt <- rep t
  case rs `compare` rt of
    EQ -> return Nothing
    LT -> do
      modify (Map.insert rt rs)
      return (Just (rt :> rs))
    GT -> do
      modify (Map.insert rs rt)
      return (Just (rs :> rt))

{-# INLINE rep #-}
rep :: Ord a => a -> UF a a
rep s = do
  m <- get
  case Map.lookup s m of
    Nothing -> return s
    Just t -> do
      u <- rep t
      when (t /= u) $ modify (Map.insert s u)
      return u
      -- case Map.lookup t m of
      --   Nothing -> return t
      --   Just u -> do
      --     v <- rep' t u
      --     modify (Map.insert s v)
      --     return v

reps :: Ord a => UF a (a -> a)
reps = do
  s <- get
  return (\x -> evalUF s (rep x))

-- rep' :: Ord a => a -> a -> UF a a
-- rep' s t = do
--   m <- get
--   case Map.lookup t m of
--     Nothing -> do
--       modify (Map.insert s t)
--       return t
--     Just u -> do
--       v <- rep' t u
--       modify (Map.insert s v)
--       return v

isRep :: Ord a => a -> UF a Bool
isRep t = do
  t' <- rep t
  return (t == t')
