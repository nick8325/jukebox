{-# LANGUAGE TypeOperators, GeneralizedNewtypeDeriving, FlexibleInstances, CPP #-}
module Jukebox.Name where

import Control.Monad
import Control.Monad.Trans.State.Strict
import Data.Ord
import Data.Int
import Data.Symbol
import Data.Char
import Data.Ratio
#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif

data Name =
    Fixed !FixedName
  | Unique {-# UNPACK #-} !Int64 String Renamer
  | Variant !Name ![Name] Renamer

data FixedName =
    Basic {-# UNPACK #-} !Symbol
  | Overloaded {-# UNPACK #-} !Symbol {-# UNPACK #-} !Symbol
  | Integer !Integer
  | Rational !Rational
  | Real !Rational
  deriving (Eq, Ord)

type Renamer = String -> Int -> Renaming
data Renaming = Renaming [String] String

base :: Named a => a -> String
base x =
  case name x of
    Fixed x -> show x
    Unique _ xs _ -> xs

instance Show FixedName where
  show (Basic xs) = unintern xs
  show (Overloaded xs _) = unintern xs
  show (Integer n) = show n
  show (Rational x) = show (numerator x) ++ "/" ++ show (denominator x)
  show (Real x) = "$to_real(" ++ show (numerator x) ++ "/" ++ show (denominator x) ++ ")"

renamer :: Named a => a -> Renamer
renamer x =
  case name x of
    Fixed _ -> defaultRenamer
    Unique _ _ f -> f
    Variant _ _ f -> f

defaultRenamer :: Renamer
defaultRenamer xs 0 = Renaming [] xs
defaultRenamer xs n = Renaming [] $ xs ++ sep ++ show (n+1)
  where
    sep
      | not (null xs) && isDigit (last xs) = "_"
      | otherwise = ""

withRenamer :: Name -> Renamer -> Name
Fixed x `withRenamer` _ = Fixed x
Unique n xs _ `withRenamer` f = Unique n xs f
Variant x xs _ `withRenamer` f = Variant x xs f

instance Eq Name where
  x == y = compareName x == compareName y

instance Ord Name where
  compare = comparing compareName

compareName :: Name -> Either FixedName (Either Int64 (Name, [Name]))
compareName (Fixed xs) = Left xs
compareName (Unique n _ _) = Right (Left n)
compareName (Variant x xs _) = Right (Right (x, xs))

instance Show Name where
  show (Fixed x) = show x
  show (Unique n xs f) = ys ++ "@" ++ show n
    where
      Renaming _ ys = f xs 0
  show (Variant x xs f) =
    "variant(" ++ show x ++
      concat [", " ++ show x | x <- xs] ++ ")"

class Named a where
  name :: a -> Name

instance Named [Char] where
  name = Fixed . Basic . intern

instance Named Name where
  name = id

variant :: (Named a, Named b) => a -> [b] -> Name
variant x xs =
  Variant (name x) (map name xs) defaultRenamer

data a ::: b = a ::: b deriving Show

lhs :: (a ::: b) -> a
lhs (x ::: _) = x

rhs :: (a ::: b) -> b
rhs (_ ::: y) = y

instance Named a => Eq (a ::: b) where s == t = name s == name t
instance Named a => Ord (a ::: b) where compare = comparing name

instance Named a => Named (a ::: b) where
  name (a ::: _) = name a

newtype NameM a =
  NameM { unNameM :: State Int64 a }
    deriving (Functor, Applicative, Monad)

runNameM :: [Name] -> NameM a -> a
runNameM xs m =
  evalState (unNameM m) (maximum (0:[ succ n | Unique n _ _ <- xs ]))

newName :: Named a => a -> NameM Name
newName x = NameM $ do
  idx <- get
  let idx' = idx+1
  when (idx' < 0) $ error "Name.newName: too many names"
  put $! idx'
  return $! Unique idx' (base x) (renamer x)
