{-# LANGUAGE BangPatterns, GeneralizedNewtypeDeriving #-}
module Jukebox.HighSat where

import MiniSat hiding (neg)
import qualified MiniSat
import qualified Jukebox.Seq as Seq
import Jukebox.Seq(Seq, List)
import Jukebox.Form(Signed(..), neg)
import qualified Jukebox.Map as Map
import Jukebox.Map(Map)
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Trans
import Data.Hashable
import Data.Traversable hiding (mapM, sequence)
import Control.Applicative
import Data.Maybe
import Data.List(partition)

newtype Sat1 a b = Sat1 { runSat1_ :: ReaderT Solver (ReaderT (Watch a) (StateT (Map a Lit) IO)) b } deriving (Functor, Monad, MonadIO)
newtype Sat a b c = Sat { runSat_ :: ReaderT (Watch a) (StateT (Map b (SatState a)) IO) c } deriving (Functor, Monad, MonadIO)
data SatState a = SatState Solver (Map a Lit)
type Watch a = a -> Sat1 a ()

data Form a
  = Lit (Signed a)
  | And (Seq (Form a))
  | Or (Seq (Form a))

nt :: Form a -> Form a
nt (Lit x) = Lit (neg x)
nt (And xs) = Or (fmap nt xs)
nt (Or xs) = And (fmap nt xs)

conj, disj :: List f => f (Form a) -> Form a
conj = And . Seq.fromList
disj = Or . Seq.fromList

true, false :: Form a
true = And Seq.Nil
false = Or Seq.Nil

unique :: List f => f (Form a) -> Form a
unique = u . Seq.toList
  where u [x] = true
        u (x:xs) = conj [disj [nt x, conj (map nt xs)],
                         u xs]

runSat :: (Hashable b, Ord b) => Watch a -> [b] -> Sat a b c -> IO c
runSat w idxs x = go idxs Map.empty
  where go [] m = evalStateT (runReaderT (runSat_ x) w) m
        go (idx:idxs) m =
          withNewSolver $ \s -> go idxs (Map.insert idx (SatState s Map.empty) m)

runSat1 :: (Ord a, Hashable a) => Watch a -> Sat1 a b -> IO b
runSat1 w x = runSat w [()] (atIndex () x)

atIndex :: (Ord a, Hashable a, Ord b, Hashable b) => b -> Sat1 a c -> Sat a b c
atIndex !idx m = do
  watch <- Sat ask
  SatState s ls <- Sat (gets (Map.findWithDefault (error "withSolver: index not found") idx))
  (x, ls') <- liftIO (runStateT (runReaderT (runReaderT (runSat1_ m) s) watch) ls)
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
