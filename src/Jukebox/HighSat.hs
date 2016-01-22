{-# LANGUAGE BangPatterns, GeneralizedNewtypeDeriving #-}
module Jukebox.HighSat where

import MiniSat hiding (neg)
import qualified MiniSat
import Jukebox.Form(Signed(..), neg)
import qualified Data.Map.Strict as Map
import Data.Map(Map)
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Trans
import Data.Traversable hiding (mapM, sequence)
import Control.Applicative
import Data.Maybe
import Data.List(partition)
import Control.Applicative

newtype Sat1 a b = Sat1 { runSat1_ :: ReaderT Solver (ReaderT (Watch a) (StateT (Map a Lit) IO)) b } deriving (Functor, Applicative, Monad, MonadIO)
newtype Sat a b c = Sat { runSat_ :: ReaderT (Watch a) (StateT (Map b (SatState a)) IO) c } deriving (Functor, Applicative, Monad, MonadIO)
data SatState a = SatState Solver (Map a Lit)
type Watch a = a -> Sat1 a ()

data Form a
  = Lit (Signed a)
  | And [Form a]
  | Or [Form a]

nt :: Form a -> Form a
nt (Lit x) = Lit (neg x)
nt (And xs) = Or (fmap nt xs)
nt (Or xs) = And (fmap nt xs)

true, false :: Form a
true = And []
false = Or []

unique :: [Form a] -> Form a
unique = u
  where u [x] = true
        u (x:xs) = And [Or [nt x, And (map nt xs)],
                        u xs]

runSat :: Ord b => Watch a -> [b] -> Sat a b c -> IO c
runSat w idxs x = go idxs Map.empty
  where go [] m = evalStateT (runReaderT (runSat_ x) w) m
        go (idx:idxs) m =
          withNewSolver $ \s -> go idxs (Map.insert idx (SatState s Map.empty) m)

runSat1 :: Ord a => Watch a -> Sat1 a b -> IO b
runSat1 w x = runSat w [()] (atIndex () x)

atIndex :: (Ord a, Ord b) => b -> Sat1 a c -> Sat a b c
atIndex !idx m = do
  watch <- Sat ask
  SatState s ls <- Sat (gets (Map.findWithDefault (error "withSolver: index not found") idx))
  (x, ls') <- liftIO (runStateT (runReaderT (runReaderT (runSat1_ m) s) watch) ls)
  Sat (modify (Map.insert idx (SatState s ls')))
  return x

solve :: Ord a => [Signed a] -> Sat1 a Bool
solve xs = do
  s <- Sat1 ask
  ls <- mapM lit xs
  liftIO (MiniSat.solve s ls)

model :: Ord a => Sat1 a (a -> Bool)
model = do
  s <- Sat1 ask
  m <- Sat1 (lift get)
  vals <- liftIO (traverse (MiniSat.modelValue s) m)
  return (\v -> fromMaybe False (Map.findWithDefault Nothing v vals))

modelValue :: Ord a => a -> Sat1 a Bool
modelValue x = do
  s <- Sat1 ask
  l <- var x
  Just b <- liftIO (MiniSat.modelValue s l)
  return b

addForm :: Ord a => Form a -> Sat1 a ()
addForm f = do
  s <- Sat1 ask
  cs <- flatten f
  liftIO (mapM (MiniSat.addClause s) cs)
  return ()

flatten :: Ord a => Form a -> Sat1 a [[Lit]]
flatten (Lit l) = fmap (return . return) (lit l)
flatten (And fs) = fmap concat (mapM flatten fs)
flatten (Or fs) = fmap (fmap concat . sequence) (mapM flatten fs)

lit :: Ord a => Signed a -> Sat1 a Lit
lit (Pos x) = var x
lit (Neg x) = liftM MiniSat.neg (var x)

var :: Ord a => a -> Sat1 a Lit
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
