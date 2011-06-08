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

data Type a = Type
  { tname :: !a,
    -- type is monotone when domain size is >= tmonotone
    tmonotone :: !DomainSize,
    -- if there is a model of size >= tsize then there is a model of size tsize
    tsize :: !DomainSize } deriving Show

instance Eq a => Eq (Type a) where
  t1 == t2 = tname t1 == tname t2

instance Ord a => Ord (Type a) where
  compare = comparing tname

-- Important that these not be strict in the type so that we can
-- "tie the knot" when doing type+monotonicity inference
data Function a = Function { fname :: !a, fres :: Type a }
data Predicate a = Predicate { pname :: !a }
data Variable a = Variable { vname :: !a, vtype :: Type a } deriving (Eq, Ord)

data Problem a b = Problem
  { types :: Map a (Type a),
    preds :: Map a ([Type a], Predicate a),
    funs :: Map a ([Type a], Function a),
    equalSize :: [[Type a]],
    inputs :: [Input b] }

data Input a = Input
  { tag :: !Tag,
    kind :: !Kind,
    formula :: !a }

instance Functor Input where
  fmap f x = x { formula = f (formula x) }

data Term a = Var !(Variable a) | !(Function a) :@: [Term a]

ty :: Term a -> Type a
ty (Var Variable{vtype = ty}) = ty
ty (Function{fres = ty} :@: _) = ty

data Atom a = !(Term a) :=: !(Term a) | !(Predicate a) :?: [Term a]

data Signed a = Pos !a | Neg !a deriving Show
type Literal a = Signed (Atom a)

data Formula a
  = Literal !(Literal a)
  | Not !(Formula a)
  | And !(AppList (Formula a))
  | Or !(AppList (Formula a))
  | Equiv !(Formula a) !(Formula a)
  | ForAll !(Set (Variable a)) !(Formula a)
  | Exists !(Set (Variable a)) !(Formula a)

data CNF a = CNF [Clause a]
data Clause a = Clause !(Set (Variable a)) [Literal a]

neg :: Signed a -> Signed a
neg (Pos x) = Neg x
neg (Neg x) = Pos x

data Kind = Axiom | NegatedConjecture deriving (Eq, Ord)
