{-# LANGUAGE ScopedTypeVariables #-}
module Formula where

import AppList(AppList)
import qualified AppList as A
import qualified Data.Set
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Hashable
import Data.HashMap(Map)
import qualified Data.HashMap as Map
import Data.Ord
import qualified Data.ByteString.Char8 as BS
import Data.List
import Utils

type Name = BS.ByteString -- for now
type Tag = BS.ByteString

data DomainSize = Finite !Int | Infinite deriving (Eq, Ord, Show)

class Names a where
  names :: Monad m => (forall a. Name a -> m (Name a)) -> a -> m a

instance Names Type where
  names f O = return O
  names f (Type name monotone size cls) = do
    name' <- f name
    return (Type name' monotone size cls)

data Type =
    O
  | Type {
      tname :: !Name,
      -- type is monotone when domain size is >= tmonotone
      tmonotone :: DomainSize,
      -- if there is a model of size >= tsize then there is a model of size tsize
      tsize :: DomainSize,
      -- two types in the same class have to have the same size
      tclass :: Int } deriving Show

instance Eq Type where
  t1 == t2 = tname t1 == tname t2

instance Ord Type where
  compare = comparing tname

instance Hashable Type where
  hashWithSalt s = hashWithSalt s . tname

data Symbol = !Name ::: !Type

instance Eq Symbol where s == t = name s == name t
instance Ord Symbol where compare = comparing name
instance Hashable Symbol where hashWithSalt s = hashWithSalt s . name

type Problem = Bind Type (Bind Function [Input])
type CNF = Bind Type (Bind Function [Bind Variable [Literal]])
-- Maybe use IntMap for names so that keys come out in ascending order?
-- Ok, but we still want variant.
-- Invariants: (name, variant) unique
-- (id, variant) unique
-- uniquify will set all variants to 0...
-- but really...
-- maybe we should have an "inefficient-string-name" part
-- which is calculated on printing out (and takes advantage of the variant)
-- and an efficient (id, variant) part
-- ...but actually, this inefficient part should just be a string paired with a number,
-- since we don't want stupid names like f_1_1_1. No, we want to avoid eagerly
-- computing the number. (Yes, the number is part of the id-thingy so we can compute it...)

data Name = Name { base :: !BS.ByteString, id :: {-# UNPACK #-} !Int, variant :: {-# UNPACK #-} !Int }
data Named a = Named { name :: {-# UNPACK #-} !Name, contents :: !a }
data Bind a b = Bind { names :: !(Map Name a), value :: !b } 

xuBINDu :: NAMESu a => -- want to only bind things of a particular type here
                   -- also, sometimes we don't want to bind all names,
                   -- e.g. in a !-quantifier.
                   -- Do we really want this Bind structure, then? What does it give us?
                   -- We want names under a binder to be maximally shared,
                   -- which a smart Bind constructor can give us,
                   -- but expecting Bind to fix all the sharing seems like a
                   -- bad idea. Actually, this smart constructor will be rather
                   -- slow if it has to rebuild the entire term from scratch.
                   -- So we should try to preserve sharing ourselves; maybe
                   -- uniquify can reintroduce sharing.
                   -- Or we can have some memoising introduce-names function...
                   -- (that's probably better)
                   -- (can even hide the name in an abstract data type so we
                   -- have to use memoisation)

data FormulaNamed a where
  Function :: Function -> FormulaNamed Function
  -- ...

names :: Formula -> [FormulaNamed a] -- or more general with monad blah

uniquify :: Names a => a -> a

data Problem f a = Problem
  { types :: Map a (Type a),
    preds :: Map a ([Type a], Predicate a),
    funs :: Map a ([Type a], Function a),
    inputs :: [Input (f a)] }

-- Get the elements of a HashMap in increasing order of size.
-- Using this instead of Data.HashMap.toList means that Equinox's
-- behaviour won't be affected by the choice of hashing function
-- (which would be scary!)
toListH :: Ord a => Map a b -> [(a, b)]
toListH = sortBy (comparing fst) . Map.toList
keysH :: Ord a => Map a b -> [a]
keysH = map fst . toListH
elemsH :: Ord a => Map a b -> [b]
elemsH = map snd . toListH

data Input a = Input
  { tag :: !Tag,
    kind :: !Kind,
    formula :: !a }

instance Functor Input where
  fmap f x = x { formula = f (formula x) }

data Term = Var !Symbol | !Symbol :@: [Term]

ty :: Term a -> Type a
ty (Var Variable{vtype = ty}) = ty
ty (Function{fres = ty} :@: _) = ty

data Atom = !Term :=: !Term | Tru !Term

data Signed a = Pos !a | Neg !a deriving Show
instance Functor Signed where
  fmap f (Pos x) = Pos (f x)
  fmap f (Neg x) = Neg (f x)
type Literal a = Signed (Atom a)

sign :: Signed a -> Signed ()
sign (Pos _) = Pos ()
sign (Neg _) = Neg ()
value :: Signed a -> a
value (Pos x) = x
value (Neg x) = x
resign :: Signed () -> a -> Signed a
resign (Pos _) = Pos
resign (Neg _) = Neg

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
rename f (Problem types preds funs inputs) =
  Problem types' preds' funs'
          (map (fmap (renameFormula f ty pred func)) inputs)
  where types' = onMap (\ty -> ty { tname = f (tname ty) }) types
        ty t = Map.findWithDefault (error "rename: type not found") (f (tname t)) types'
        preds' = onMap (\(xs, p) -> (map ty xs, Predicate (f (pname p)))) preds
        funs' = onMap (\(xs, fun) -> (map ty xs, Function (f (fname fun)) (ty (fres fun)))) funs
        pred p = snd (Map.findWithDefault (error "rename: predicate not found") (f (pname p)) preds')
        func fun = snd (Map.findWithDefault (error "rename: function not found") (f (fname fun)) funs')
        onMap g m = Map.fromList . map (\(x, y) -> (f x, g y)) . Map.toList $ m

-- Return all names that appear in a problem.
names :: Problem Formula a -> [a]
names (Problem types preds funs inputs) =
  concat [Map.keys types, Map.keys preds, Map.keys funs,
          A.toList (A.concat (map (vars . formula) inputs))]
    where vars (Literal (Pos a)) = atom a
          vars (Literal (Neg a)) = atom a
          vars (Not f) = vars f
          vars (And fs) = A.concat (fmap vars fs)
          vars (Or fs) = A.concat (fmap vars fs)
          vars (Equiv f g) = vars f `A.append` vars g
          vars (ForAll xs f) = map vname (Set.toList xs) `A.append` vars f
          vars (Exists xs f) = map vname (Set.toList xs) `A.append` vars f
          atom (t :=: u) = term t `A.append` term u
          atom (p :?: xs) = A.concat (map term xs)
          term (f :@: xs) = A.concat (map term xs)
          term (Var v) = A.Unit (vname v)

-- A function for generating unique names.
-- Given a problem of type Problem Formula a, and a function a -> Name
-- (which might not be injective on the set of names in the problem,
-- i.e. some names might be mapped to the same Name),
-- produce a function a -> Name that is injective,
-- by adding a numeric suffix to the generated Names.
name :: forall a. (Ord a, Hashable a) => (a -> Name) -> Problem Formula a -> (a -> Name)
name base p = f
  where nameMap :: Map Name (Map a Int)
        nameMap =
          -- Assign numbers to each name
          Map.map (\xs -> Map.fromList (zip (usort xs) [0..])).
          -- Partition by basename
          foldl' (\m x -> Map.insertWith (++) (base x) [x] m) Map.empty .
          names $ p
        f x = combine (base x) b
          where b = Map.findWithDefault (error "name: name not found") x
                    (Map.findWithDefault (error "name: name not found") (base x) nameMap)
        combine s 0 = s
        combine s n = uniquify (BS.append s (BS.pack ('_':show n)))
        uniquify s | not (Map.member s nameMap) = s
                   | otherwise = 
                     -- Odd situation: we have e.g. a name with basename "f_1",
                     -- and two names with basename "f", which would normally
                     -- become "f" and "f_1", but the "f_1" conflicts.
                     -- Try appending some suffix.
                     uniquify (BS.snoc s 'a')
