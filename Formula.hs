{-# LANGUAGE TypeOperators #-}
module Formula where

import qualified AppList as A
import AppList(AppList)
import Data.Hashable
import qualified Data.HashMap as Map
import NameMap(NameMap)
import Data.Ord
import qualified Data.ByteString.Char8 as BS
import Name
import Control.Monad

type Tag = BS.ByteString

data a ::: b = !a ::: !b

instance Named a => Eq (a ::: b) where s == t = name s == name t
instance Named a => Ord (a ::: b) where compare = comparing name
instance Named a => Hashable (a ::: b) where hashWithSalt s = hashWithSalt s . name

instance Named a => Named (a ::: b) where
  name (a ::: b) = name a

data DomainSize = Finite !Int | Infinite deriving (Eq, Ord, Show)

data Type =
    O
  | Type {
      tname :: {-# UNPACK #-} !Name,
      -- type is monotone when domain size is >= tmonotone
      tmonotone :: DomainSize,
      -- if there is a model of size >= tsize then there is a model of size tsize
      tsize :: DomainSize,
      -- two types in the same class have to have the same size
      tclass :: Int } deriving Show

data FunType = FunType { args :: [Type], res :: !Type } deriving Eq

instance Eq Type where
  O == O = True
  Type { tname = t1 } == Type { tname = t2 } = t1 == t2
  _ == _ = False

instance Ord Type where
  compare O O = EQ
  compare O Type{} = LT
  compare Type{} O = GT
  compare Type{tname = t1} Type{tname = t2} = compare t1 t2

instance Hashable Type where
  hashWithSalt s = hashWithSalt s . toMaybe
    where toMaybe O = Nothing
          toMaybe Type { tname = t } = Just t

instance Named Type where
  name O = nameO
  name Type{tname = t} = t

class Typed a where
  typ :: a -> Type

instance Typed Type where
  typ = id

instance Typed FunType where
  typ = res
  
instance Typed b => Typed (a ::: b) where
  typ (_ ::: t) = typ t

type Problem a = Closed [Input a]

data Input a = Input
  { tag :: !Tag,
    kind :: !Kind,
    formula :: !a }

instance Functor Input where
  fmap f x = x { formula = f (formula x) }

type Variable = Name ::: Type
type Function = Name ::: FunType
data Term = Var !Variable | !Function :@: [Term]

instance Named Term where
  name (Var x) = name x
  name (f :@: _) = name f

instance Typed Term where
  typ (Var x) = typ x
  typ (f :@: _) = typ f

data Atomic = !Term :=: !Term | Tru !Term
data Signed a = Pos !a | Neg !a deriving Show

instance Functor Signed where
  fmap f (Pos x) = Pos (f x)
  fmap f (Neg x) = Neg (f x)
type Literal = Signed Atomic

data Formula
  = Literal !Literal
  | Not !Formula
  | And !(AppList Formula)
  | Or !(AppList Formula)
  | Equiv !Formula !Formula
  | ForAll !(NameMap Variable) !Formula
  | Exists !(NameMap Variable) !Formula

neg :: Signed a -> Signed a
neg (Pos x) = Neg x
neg (Neg x) = Pos x

data Kind = Axiom | NegatedConjecture deriving (Eq, Ord)

class Symbolic a where
  terms :: a -> AppList Term
  boundVars :: a -> AppList Variable

vars :: Symbolic a => a -> AppList Variable
vars s = boundVars s `mplus` do
  Var x <- terms s
  return x

functions :: Symbolic a => a -> AppList Function
functions s = do
  f :@: _ <- terms s
  return f

types :: Symbolic a => a -> AppList Type
types s = fmap typ (boundVars s) `mplus` fmap typ (terms s)

names :: Symbolic a => a -> AppList Name
names s = fmap name (boundVars s) `mplus` do
  x <- terms s
  return (name x) `mplus` return (name (typ x))

instance Symbolic Formula where
  terms (Literal l) = terms l
  terms (Not f) = terms f
  terms (And xs) = A.concat (fmap terms xs)
  terms (Or xs) = A.concat (fmap terms xs)
  terms (Equiv t u) = terms t `A.append` terms u
  terms (ForAll _ t) = terms t
  terms (Exists _ t) = terms t
  
  boundVars (Literal _) = A.Nil
  boundVars (Not f) = boundVars f
  boundVars (And xs) = A.concat (fmap boundVars xs)
  boundVars (Or xs) = A.concat (fmap boundVars xs)
  boundVars (Equiv t u) = boundVars t `A.append` boundVars u
  boundVars (ForAll x t) = A.fromList (Map.elems x) `A.append` boundVars t
  boundVars (Exists x t) = A.fromList (Map.elems x) `A.append` boundVars t

instance Symbolic a => Symbolic (Signed a) where
  terms (Pos x) = terms x
  terms (Neg x) = terms x
  boundVars (Pos x) = boundVars x
  boundVars (Neg x) = boundVars x

instance Symbolic Atomic where
  terms (t :=: u) = terms t `A.append` terms u
  boundVars (t :=: u) = boundVars t `A.append` boundVars u

instance Symbolic Term where
  terms t@Var{} = A.Unit t
  terms t@(_ :@: ts) = A.Unit t `A.append` A.concat (fmap terms ts)
  
  boundVars _ = A.Nil

instance Symbolic a => Symbolic (Input a) where
  boundVars = boundVars . formula
  terms = terms . formula
  
instance Symbolic a => Symbolic [a] where
  boundVars = A.concat . map boundVars
  terms = A.concat . map terms
