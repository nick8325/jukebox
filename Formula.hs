module Formula where

import AppList(AppList)
import qualified AppList
import qualified Data.Set
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Hashable
import Data.HashMap(Map)
import qualified Data.HashMap as Map
import qualified Data.HashSet as HashSet
import Data.Ord
import qualified Data.ByteString.Char8 as BS
import Data.List
import Control.Monad.State.Strict

type Name = BS.ByteString -- for now
type Tag = BS.ByteString

data DomainSize = Finite !Int | Infinite deriving (Eq, Ord, Show)

data Type a = Type
  { tname :: !a,
    -- type is monotone when domain size is >= tmonotone
    tmonotone :: DomainSize,
    -- if there is a model of size >= tsize then there is a model of size tsize
    tsize :: DomainSize } deriving Show

instance Eq a => Eq (Type a) where
  t1 == t2 = tname t1 == tname t2

instance Ord a => Ord (Type a) where
  compare = comparing tname

instance Hashable a => Hashable (Type a) where
  hashWithSalt s = hashWithSalt s . tname

-- Important that these not be strict in the type so that we can
-- "tie the knot" when doing type+monotonicity inference
data Function a = Function { fname :: !a, fres :: Type a }
data Predicate a = Predicate { pname :: !a }
data Variable a = Variable { vname :: !a, vtype :: Type a } deriving (Eq, Ord)

data Problem f a = Problem
  { types :: Map a (Type a),
    preds :: Map a ([Type a], Predicate a),
    funs :: Map a ([Type a], Function a),
    equalSize :: [[Type a]],
    inputs :: [Input (f a)] }

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
instance Functor Signed where
  fmap f (Pos x) = Pos (f x)
  fmap f (Neg x) = Neg (f x)
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

-- Tidy this up later.
-- Formula renaming.

renameFormula :: Ord b => (a -> b) -> (Type a -> Type b) ->
                 (Predicate a -> Predicate b) ->
                 (Function a -> Function b) ->
                 Formula a -> Formula b
renameFormula name ty pred fun = form
  where form (Literal l) = Literal (fmap atom l)
        form (Not f) = Not (form f)
        form (And fs) = And (fmap form fs)
        form (Or fs) = Or (fmap form fs)
        form (Equiv f g) = Equiv (form f) (form g)
        form (ForAll xs f) = ForAll (mapSet var xs) (form f)
        form (Exists xs f) = Exists (mapSet var xs) (form f)
        atom (t :=: u) = term t :=: term u
        atom (p :?: xs) = pred p :?: map term xs
        term (Var x) = Var (var x)
        term (f :@: xs) = fun f :@: map term xs
        var (Variable x typ) = Variable (name x) (ty typ)
        -- Set.map has an unnecessary Ord a constraint.
        mapSet f = Set.fromList . map f . Set.toList

rename :: (Ord b, Hashable b) => (a -> b) -> Problem Formula a -> Problem Formula b
rename f (Problem types preds funs equalSize inputs) =
  Problem types' preds' funs' (map (map ty) equalSize)
          (map (fmap (renameFormula f ty pred func)) inputs)
  where types' = onMap (\ty -> ty { tname = f (tname ty) }) types
        ty t = Map.findWithDefault (error "rename: type not found") (f (tname t)) types'
        preds' = onMap (\(xs, p) -> (map ty xs, Predicate (f (pname p)))) preds
        funs' = onMap (\(xs, fun) -> (map ty xs, Function (f (fname fun)) (ty (fres fun)))) funs
        pred p = snd (Map.findWithDefault (error "rename: predicate not found") (f (pname p)) preds')
        func fun = snd (Map.findWithDefault (error "rename: function not found") (f (fname fun)) funs')
        onMap g m | Map.size m' /= Map.size m = error "rename: non-injective rename"
                  | otherwise = m'
          where m' = Map.fromList . map (\(x, y) -> (f x, g y)) . Map.toList $ m

names :: Problem Formula a -> [a]
names (Problem types preds funs equalSize inputs) =
  concat [Map.keys types, Map.keys preds, Map.keys funs,
          AppList.toList (AppList.concat (AppList.fromList (map (vars . formula) inputs)))]
    where vars (Literal (Pos a)) = atom a
          vars (Literal (Neg a)) = atom a
          vars (Not f) = vars f
          vars (And fs) = AppList.concat (fmap vars fs)
          vars (Or fs) = AppList.concat (fmap vars fs)
          vars (Equiv f g) = vars f `AppList.append` vars g
          vars (ForAll xs f) = AppList.fromList (map vname (Set.toList xs)) `AppList.append` vars f
          vars (Exists xs f) = AppList.fromList (map vname (Set.toList xs)) `AppList.append` vars f
          atom (t :=: u) = term t `AppList.append` term u
          atom (p :?: xs) = AppList.concat (AppList.fromList (map term xs))
          term (f :@: xs) = AppList.concat (AppList.fromList (map term xs))
          term (Var v) = AppList.Unit (vname v)

-- uniquify :: (Ord a, Hashable a) => (a -> Name) -> Problem a (Formula a) -> Problem Name (Formula Name)
-- uniquify base p =

