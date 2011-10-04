{-# LANGUAGE BangPatterns, GeneralizedNewtypeDeriving #-}
module Sat where

import MiniSat
import qualified MiniSat
import qualified Seq as Seq
import Seq(Seq, List)
import Form(Signed(..))
import qualified Data.HashMap as Map
import Data.HashMap(Map)
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Trans
import Data.Hashable
import Data.Traversable hiding (mapM, sequence)
import Control.Applicative
import Data.Maybe
import Data.List(partition)

newtype Sat1 a b = Sat1 { runSat1 :: ReaderT Solver (ReaderT (Watch a) (StateT (Map a Lit) IO)) b } deriving (Functor, Monad, MonadIO)
newtype Sat a b c = Sat { runSat_ :: ReaderT (Watch a) (StateT (Map b (SatState a)) IO) c } deriving (Functor, Monad, MonadIO)
data SatState a = SatState Solver (Map a Lit)
type Watch a = a -> Sat1 a ()

data Form a
  = Lit (Signed a)
  | And (Seq (Form a))
  | Or (Seq (Form a))

conj, disj :: List f => f (Form a) -> Form a
conj = And . Seq.fromList
disj = Or . Seq.fromList

true, false :: Form a
true = And Seq.Nil
false = Or Seq.Nil

runSat :: (Hashable b, Ord b) => Watch a -> [b] -> Sat a b c -> IO c
runSat w idxs x = go idxs Map.empty
  where go [] m = evalStateT (runReaderT (runSat_ x) w) m
        go (idx:idxs) m =
          withNewSolver $ \s -> go idxs (Map.insert idx (SatState s Map.empty) m)

atIndex :: (Ord a, Hashable a, Ord b, Hashable b) => b -> Sat1 a c -> Sat a b c
atIndex !idx m = do
  watch <- Sat ask
  SatState s ls <- Sat (gets (Map.findWithDefault (error "withSolver: index not found") idx))
  (x, ls') <- liftIO (runStateT (runReaderT (runReaderT (runSat1 m) s) watch) ls)
  Sat (modify (Map.insert idx (SatState s ls')))
  return x

solve :: (Ord a, Hashable a) => [Signed a] -> Sat1 a Bool
solve xs = do
  s <- Sat1 ask
  ls <- mapM lit xs
  liftIO (MiniSat.solve s ls)

model :: (Ord a, Hashable a) => Sat1 a (a -> Bool)
model = do
  s <- Sat1 ask
  m <- Sat1 (lift get)
  vals <- liftIO (traverse (MiniSat.modelValue s) m)
  return (\v -> fromMaybe False (Map.findWithDefault Nothing v vals))

modelValue :: (Ord a, Hashable a) => a -> Sat1 a Bool
modelValue x = do
  s <- Sat1 ask
  l <- var x
  Just b <- liftIO (MiniSat.modelValue s l)
  return b

addForm :: (Ord a, Hashable a) => Form a -> Sat1 a ()
addForm f = do
  s <- Sat1 ask
  cs <- flatten f
  liftIO (Seq.mapM (MiniSat.addClause s . Seq.toList) cs)
  return ()

flatten :: (Ord a, Hashable a) => Form a -> Sat1 a (Seq (Seq Lit))
flatten (Lit l) = fmap (Seq.Unit . Seq.Unit) (lit l)
flatten (And fs) = fmap Seq.concat (Seq.mapM flatten fs)
flatten (Or fs) = fmap (fmap Seq.concat . Seq.sequence) (Seq.mapM flatten fs)

lit :: (Ord a, Hashable a) => Signed a -> Sat1 a Lit
lit (Pos x) = var x
lit (Neg x) = liftM MiniSat.neg (var x)

var :: (Ord a, Hashable a) => a -> Sat1 a Lit
var x = do
  s <- Sat1 ask
  m <- Sat1 get
  case Map.lookup x m of
    Nothing -> do
      l <- liftIO (MiniSat.newLit s)
      Sat1 (put (Map.insert x l m))
      w <- Sat1 (lift ask)
      w x
      return l
    Just l -> return l
