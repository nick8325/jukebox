module Formula where

import AppList(AppList)
import qualified AppList
import qualified Data.Set
import Data.Set(Set)
import qualified Data.Set as Set
import Data.HashMap(Map)
import qualified Data.HashMap as Map
import Data.Ord
import qualified Data.ByteString.Char8 as BS
import Data.List

type Name = BS.ByteString -- for now
type Tag = BS.ByteString

data DomainSize = Finite !Int | Infinite deriving (Eq, Ord, Show)

data Type = Type
  { tname :: !Name,
    -- type is monotone when domain size is >= tmonotone
    tmonotone :: !DomainSize,
    -- if there is a model of size >= tsize then there is a model of size tsize
    tsize :: !DomainSize } deriving Show

instance Eq Type where
  t1 == t2 = tname t1 == tname t2

instance Ord Type where
  compare = comparing tname

data Function = Function { fname :: !Name, fres :: !Type }
data Predicate = Predicate { pname :: !Name }
data Variable = Variable { vname :: !Name, vtype :: !Type } deriving (Eq, Ord)

data Problem a = Problem
  { types :: Map BS.ByteString Type,
    preds :: Map BS.ByteString ([Type], Predicate),
    funs :: Map BS.ByteString ([Type], Function),
    inputs :: [Input a] }

data Input a = Input
  { tag :: !Tag,
    kind :: !Kind,
    formula :: !a }

instance Functor Input where
  fmap f x = x { formula = f (formula x) }

data Term = Var !Variable | !Function :@: [Term]

ty :: Term -> Type
ty (Var Variable{vtype = ty}) = ty
ty (Function{fres = ty} :@: _) = ty

data Atom = Term :=: Term | !Predicate :?: [Term]

data Signed a = Pos !a | Neg !a deriving Show
type Literal = Signed Atom

data Formula
  = Literal !Literal
  | Not !Formula
  | And !(AppList Formula)
  | Or !(AppList Formula)
  | Equiv !Formula !Formula
  | ForAll !(Set Variable) !Formula
  | Exists !(Set Variable) !Formula

data CNF = CNF [Clause]
data Clause = Clause !(Set Variable) [Literal]

neg :: Signed a -> Signed a
neg (Pos x) = Neg x
neg (Neg x) = Pos x

data Kind = Axiom | NegatedConjecture deriving (Eq, Ord)
