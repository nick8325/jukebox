{-# LANGUAGE TypeOperators #-}
module Form where

import qualified Seq as S
import Seq(Seq)
import Data.Hashable
import qualified Data.HashMap as Map
import NameMap(NameMap)
import qualified NameMap
import Data.Ord
import qualified Data.ByteString.Char8 as BS
import Name
import Control.Monad
import Data.Monoid

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
  { tag ::  !Tag,
    kind :: !Kind,
    what :: !a }

instance Functor Input where
  fmap f x = x { what = f (what x) }

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

data Form
  = Literal !Literal
  | Not !Form
  | And !(Seq Form)
  | Or !(Seq Form)
  | Equiv !Form !Form
  | ForAll !(NameMap Variable) !Form
  | Exists !(NameMap Variable) !Form

true, false :: Form
true = And S.Nil
false = Or S.Nil

isTrue, isFalse :: Form -> Bool
isTrue (And S.Nil) = True
isTrue _ = False
isFalse (Or S.Nil) = True
isFalse _ = False

nt :: Form -> Form
nt (Not a) = a
nt a       = Not a

(.=>) :: Form -> Form -> Form
p .=> q = nt p \/ q

(/\), (\/) :: Form -> Form -> Form
And as /\ And bs = And (as `S.append` bs)
a      /\ b | isFalse a || isFalse b = false
And as /\ b      = And (b `S.cons` as)
a      /\ And bs = And (a `S.cons` bs)
a      /\ b      = And (S.Unit a `S.append` S.Unit b)

Or as \/ Or bs = Or (as `S.append` bs)
a     \/ b | isTrue a || isTrue b = true
Or as \/ b     = Or (b `S.cons` as)
a     \/ Or bs = Or (a `S.cons` bs)
a     \/ b     = Or (S.Unit a `S.append` S.Unit b)

-- remove Not from a problem, replacing it with negated literals
positive :: Form -> Form
positive (Not (And as))      = Or (fmap nt as)
positive (Not (Or as))       = And (fmap nt as)
positive (Not (a `Equiv` b)) = nt a `Equiv` b
positive (Not (Not a))       = positive a
positive (Not (ForAll v a))  = Exists v (nt a)
positive (Not (Exists v a))  = ForAll v (nt a)
positive (Not (Literal l))   = Literal (neg l)
positive a                   = a

simple :: Form -> Form
simple (Or as)       = Not (And (fmap nt as))
simple (Exists vs a) = Not (ForAll vs (nt a))
simple a             = a

type Subst = NameMap (Name ::: Term)

ids :: Subst
ids = Map.empty

(|=>) :: Named a => a -> Term -> Subst
v |=> x = NameMap.singleton (name v ::: x)

(|+|) :: Subst -> Subst -> Subst
(|+|) = Map.union

type Clause = [Signed Atomic]
data QClause = Clause !(NameMap Variable) !Clause

toQClause :: Clause -> QClause
toQClause c = Clause (NameMap.fromList (vars c)) c

toForm :: QClause -> Form
toForm (Clause xs ls) = ForAll xs (And (S.fromList (map Literal ls)))

neg :: Signed a -> Signed a
neg (Pos x) = Neg x
neg (Neg x) = Pos x

the :: Signed a -> a
the (Pos x) = x
the (Neg x) = x

pos :: Signed a -> Bool
pos (Pos _) = True
pos (Neg _) = False

data Kind = Axiom | NegatedConjecture deriving (Eq, Ord)

class Symbolic a where
  terms :: a -> Seq Term
  boundVars :: a -> Seq Variable
  free :: a -> NameMap Variable
  subst :: Subst -> a -> a

vars :: Symbolic a => a -> Seq Variable
vars s = boundVars s `mplus` do
  Var x <- terms s
  return x

functions :: Symbolic a => a -> Seq Function
functions s = do
  f :@: _ <- terms s
  return f

types :: Symbolic a => a -> Seq Type
types s = fmap typ (boundVars s) `mplus` fmap typ (terms s)

names :: Symbolic a => a -> Seq Name
names s = fmap name (boundVars s) `mplus` do
  x <- terms s
  return (name x) `mplus` return (name (typ x))

instance Symbolic Form where
  terms (Literal l) = terms l
  terms (Not f) = terms f
  terms (And xs) = S.concat (fmap terms xs)
  terms (Or xs) = S.concat (fmap terms xs)
  terms (Equiv t u) = terms t `S.append` terms u
  terms (ForAll _ t) = terms t
  terms (Exists _ t) = terms t
  
  boundVars (Literal _) = S.Nil
  boundVars (Not f) = boundVars f
  boundVars (And xs) = S.concat (fmap boundVars xs)
  boundVars (Or xs) = S.concat (fmap boundVars xs)
  boundVars (Equiv t u) = boundVars t `S.append` boundVars u
  boundVars (ForAll x t) = S.fromList (Map.elems x) `S.append` boundVars t
  boundVars (Exists x t) = S.fromList (Map.elems x) `S.append` boundVars t

instance Symbolic a => Symbolic (Signed a) where
  terms (Pos x) = terms x
  terms (Neg x) = terms x
  boundVars (Pos x) = boundVars x
  boundVars (Neg x) = boundVars x

instance Symbolic Atomic where
  terms (t :=: u) = terms t `S.append` terms u
  boundVars (t :=: u) = boundVars t `S.append` boundVars u

instance Symbolic Term where
  terms t@Var{} = S.Unit t
  terms t@(_ :@: ts) = S.Unit t `S.append` S.concat (fmap terms ts)
  
  boundVars _ = S.Nil

instance Symbolic a => Symbolic (Input a) where
  boundVars = boundVars . what
  terms = terms . what
  
instance Symbolic a => Symbolic [a] where
  boundVars = S.concat . map boundVars
  terms = S.concat . map terms

uniqueNames :: Form -> NameM Form
uniqueNames = undefined
