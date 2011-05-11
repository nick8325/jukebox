module Formula where

import AppList(AppList)
import qualified Data.Set
import Data.Set(Set)
import Data.Map(Map)
import Data.Ord
import qualified Data.ByteString.Char8 as BS
import Data.List
import ReadProblem.Syntax(Tag)

type Name = BS.ByteString -- for now

data DomainSize = Finite !Int | Infinite deriving (Eq, Ord) 

data Type = Type
  { tname :: !Name,
    -- type is monotone when domain size is >= tmonotone
    tmonotone :: !DomainSize,
    -- if there is a model of size >= tsize then there is a model of size tsize
    tsize :: !DomainSize }

instance Eq Type where
  t1 == t2 = tname t1 == tname t2

instance Ord Type where
  compare = comparing tname

instance Show Type where
  show = BS.unpack . tname

data Function = Function { fname :: !Name, fres :: !Type } deriving Show
data Predicate = Predicate { pname :: !Name } deriving Show
data Variable = Variable { vname :: !Name, vtype :: !Type } deriving (Eq, Ord, Show)

data Problem a = Problem
  { types :: Map BS.ByteString Type,
    preds :: Map BS.ByteString ([Type], Predicate),
    funs :: Map BS.ByteString ([Type], Function),
    inputs :: [Input a] } deriving Show

data Input k a = Input
  { tag :: !Tag,
    kind :: !Kind,
    formula :: !a } deriving Show

instance Functor Input where
  fmap f x = x { formula = f (formula x) }

data Term = Var !Variable | !Function :@: [Term] deriving Show
data Atom = Term :=: Term | !Predicate :?: [Term] deriving Show
data Signed a = Pos !a | Neg !a deriving Show
type Literal = Signed Atom

data Formula
  = Literal !Literal
  | And !(AppList Formula)
  | Or !(AppList Formula)
  | Equiv !Formula !Formula
  | ForAll !(Set Variable) !Formula
  | Exists !(Set Variable) !Formula deriving Show

data CNF = CNF [Clause]
data Clause = Clause !(Set Variable) [Literal]

nt :: Formula -> Formula
nt (Literal x) = Literal (neg x)
nt (And xs) = Or (fmap nt xs)
nt (Or xs) = And (fmap nt xs)
nt (Equiv x y) = Equiv (nt x) y
nt (ForAll vs x) = Exists vs (nt x)
nt (Exists vs x) = ForAll vs (nt x)

neg :: Signed a -> Signed a
neg (Pos x) = Neg x
neg (Neg x) = Pos x

data Kind = Axiom | NegatedConjecture deriving (Eq, Ord, Show)

showPredType args = showArgs args ++ "$o"
showFunType args res = showArgs args ++ show res
showArgs [] = ""
showArgs [ty] = show ty ++ " > "
showArgs tys = "(" ++ intercalate " * " (map show tys) ++ ") >"
