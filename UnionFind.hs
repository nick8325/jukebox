module UnionFind(UF, Replacement((:>)), (=:=), rep, evalUF, execUF, runUF, S, isRep, initial) where

import Prelude hiding (min)
import Control.Monad.State.Strict
import Data.Hashable
import Data.Map(Map)
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

(=:=) :: (Hashable a, Ord a) => a -> a -> UF a (Maybe (Replacement a))
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

rep :: (Hashable a, Ord a) => a -> UF a a
rep t = do
  m <- get
  case Map.lookup t m of
    Nothing -> return t
    Just t' -> do
      r <- rep t'
      when (t' /= r) $ put (Map.insert t r m)
      return r

isRep :: (Hashable a, Ord a) => a -> UF a Bool
isRep t = do
  t' <- rep t
  return (t == t')
