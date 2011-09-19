{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Sat where

import MiniSat
import qualified MiniSat
import qualified Seq as Seq
import Seq(Seq, List)
import Form(Signed(..))
import qualified Data.HashMap as Map
import Data.HashMap(Map)
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Trans
import Data.Hashable
import Data.Traversable hiding (mapM, sequence)
import Control.Applicative
import Data.Maybe

newtype Sat a b = Sat { runSat_ :: ReaderT Solver (ReaderT (Watch a) (StateT (Map a Lit) IO)) b } deriving (Functor, Monad, MonadIO)
type Watch a = a -> Sat a ()

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

runSat :: Watch a -> Sat a b -> IO b
runSat w x =
  MiniSat.withNewSolver $ \s ->
    evalStateT (runReaderT (runReaderT (runSat_ x) s) w) Map.empty

solve :: (Ord a, Hashable a) => [Signed a] -> Sat a Bool
solve xs = do
  s <- Sat ask
  ls <- mapM lit xs
  liftIO (MiniSat.solve s ls)

model :: (Ord a, Hashable a) => Sat a (a -> Bool)
model = do
  s <- Sat ask
  m <- Sat (lift get)
  vals <- liftIO (traverse (MiniSat.modelValue s) m)
  return (\v -> fromMaybe False (Map.findWithDefault Nothing v vals))

modelValue :: (Ord a, Hashable a) => a -> Sat a Bool
modelValue x = do
  s <- Sat ask
  l <- var x
  Just b <- liftIO (MiniSat.modelValue s l)
  return b

addForm :: (Ord a, Hashable a) => Form a -> Sat a ()
addForm c = do
 s <- Sat ask
 toClauses c >>= liftIO . mapM (MiniSat.addClause s) . map Seq.toList . Seq.toList
 return ()

toClauses :: (Ord a, Hashable a) => Form a -> Sat a (Seq (Seq Lit))
toClauses (And fs) = fmap Seq.concat (Seq.mapM toClauses fs)
toClauses (Or (Seq.Unit f)) = toClauses f
toClauses f = fmap Seq.Unit (toClause f)

toClause :: (Ord a, Hashable a) => Form a -> Sat a (Seq Lit)
toClause (Lit l) = fmap (Seq.Unit) (lit l)
toClause (Or fs) = fmap Seq.concat (Seq.mapM toClause fs)
toClause (And (Seq.Unit f)) = toClause f
toClause f = do
  s <- Sat ask
  l <- liftIO (newLit s)
  cs <- toClauses f
  Seq.mapM (liftIO . MiniSat.addClause s) (fmap ((l:) . Seq.toList) cs)
  return (Seq.Unit l)

lit :: (Ord a, Hashable a) => Signed a -> Sat a Lit
lit (Pos x) = var x
lit (Neg x) = liftM MiniSat.neg (var x)

var :: (Ord a, Hashable a) => a -> Sat a Lit
var x = do
  s <- Sat ask
  m <- Sat (lift get)
  case Map.lookup x m of
    Nothing -> do
      l <- liftIO (MiniSat.newLit s)
      Sat (lift (put (Map.insert x l m)))
      w <- Sat (lift ask)
      w x
      return l
    Just l -> return l
