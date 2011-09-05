-- Formulae, inputs, terms and so on.
--
-- "Show" instances for several of these types are found in TPTP.Print.

{-# LANGUAGE FlexibleContexts, Rank2Types, GADTs, TypeOperators, ScopedTypeVariables #-}
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
import qualified Changing as C

----------------------------------------------------------------------
-- Types

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

-- Helper function for defining (Eq, Ord, Hashable) instances
typeMaybeName :: Type -> Maybe Name
typeMaybeName O = Nothing
typeMaybeName Type{tname = t} = Just t

instance Eq Type where
  t1 == t2 = typeMaybeName t1 == typeMaybeName t2

instance Ord Type where
  compare = comparing typeMaybeName

instance Hashable Type where
  hashWithSalt s = hashWithSalt s . typeMaybeName

instance Named Type where
  name O = nameO
  name Type{tname = t} = t

-- Typeclass of "things that have a type"
class Typed a where
  typ :: a -> Type

instance Typed Type where
  typ = id

instance Typed FunType where
  typ = res

----------------------------------------------------------------------
-- Terms

data a ::: b = !a ::: !b

instance Named a => Eq (a ::: b) where s == t = name s == name t
instance Named a => Ord (a ::: b) where compare = comparing name
instance Named a => Hashable (a ::: b) where hashWithSalt s = hashWithSalt s . name

instance Named a => Named (a ::: b) where
  name (a ::: b) = name a
  
instance Typed b => Typed (a ::: b) where
  typ (_ ::: t) = typ t

type Variable = Name ::: Type
type Function = Name ::: FunType
data Term = Var !Variable | !Function :@: [Term]

instance Named Term where
  name (Var x) = name x
  name (f :@: _) = name f

instance Typed Term where
  typ (Var x) = typ x
  typ (f :@: _) = typ f

----------------------------------------------------------------------
-- Literals

data Atomic = !Term :=: !Term | Tru !Term
data Signed a = Pos !a | Neg !a deriving Show

instance Functor Signed where
  fmap f (Pos x) = Pos (f x)
  fmap f (Neg x) = Neg (f x)
type Literal = Signed Atomic

neg :: Signed a -> Signed a
neg (Pos x) = Neg x
neg (Neg x) = Pos x

the :: Signed a -> a
the (Pos x) = x
the (Neg x) = x

pos :: Signed a -> Bool
pos (Pos _) = True
pos (Neg _) = False

----------------------------------------------------------------------
-- Formulae

data Form
  = Literal Literal
  | Not Form
  | And (Seq Form)
  | Or (Seq Form)
  | Equiv Form Form
  | ForAll (Bind Form)
  | Exists (Bind Form)

data Bind a = Bind !(NameMap Variable) !a

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
positive (Not (And as))             = Or (fmap nt as)
positive (Not (Or as))              = And (fmap nt as)
positive (Not (a `Equiv` b))        = nt a `Equiv` b
positive (Not (Not a))              = positive a
positive (Not (ForAll (Bind vs a))) = Exists (Bind vs (nt a))
positive (Not (Exists (Bind vs a))) = ForAll (Bind vs (nt a))
positive (Not (Literal l))          = Literal (neg l)
positive a                          = a

-- remove Exists and Or from the top level of a formula
simple :: Form -> Form
simple (Or as)              = Not (And (fmap nt as))
simple (Exists (Bind vs a)) = Not (ForAll (Bind vs (nt a)))
simple a                    = a

-- perform some easy algebraic simplifications
simplify t@Literal{} = t
simplify (Not (Literal l)) = Literal (neg l)
simplify (Not (Not t)) = simplify t
simplify (Not t) = Not (simplify t)
simplify (And ts) = S.fold (/\) id true (fmap simplify ts)
simplify (Or ts) = S.fold (\/) id false (fmap simplify ts)
simplify (Equiv t u) = equiv t u
  where equiv t u | isTrue t = u
                  | isTrue u = t
                  | isFalse t = nt u
                  | isFalse u = nt t
                  | otherwise = Equiv t u
simplify (ForAll (Bind vs t)) = forAll vs (simplify t)
  where forAll vs t | Map.null vs = t
        forAll vs (ForAll (Bind vs' t)) = ForAll (Bind (Map.union vs vs') t)
        forAll vs t = ForAll (Bind vs t)
simplify (Exists (Bind vs t)) = exists vs (simplify t)
  where exists vs t | Map.null vs = t
        exists vs (Exists (Bind vs' t)) = Exists (Bind (Map.union vs vs') t)
        exists vs t = Exists (Bind vs t)

----------------------------------------------------------------------
-- Substitutions

type Subst = NameMap (Name ::: Term)

ids :: Subst
ids = Map.empty

(|=>) :: Named a => a -> Term -> Subst
v |=> x = NameMap.singleton (name v ::: x)

(|+|) :: Subst -> Subst -> Subst
(|+|) = Map.union

----------------------------------------------------------------------
-- Clauses

newtype Clause = Clause [Signed Atomic]

toForm :: Bind Clause -> Form
toForm (Bind xs (Clause ls)) = ForAll (Bind xs (And (S.fromList (map Literal ls))))

----------------------------------------------------------------------
-- Problems

type Tag = BS.ByteString

data Kind = Axiom | NegatedConjecture deriving (Eq, Ord)

data Input a = Input
  { tag ::  !Tag,
    kind :: !Kind,
    what :: !a }

type Problem a = Closed [Input a]

instance Functor Input where
  fmap f x = x { what = f (what x) }

----------------------------------------------------------------------
-- Symbolic stuff

-- A universe of types
data TypeRep a where
  FormRep :: TypeRep Form
  ClauseRep :: TypeRep Clause
  TermRep :: TypeRep Term
  AtomicRep :: TypeRep Atomic
  -- The Symbolic (Signed a) etc. witnesses are unnecessary
  -- but cause GHC to generate better code
  -- (without them it needlessly recomputes the dictionaries)
  SignedRep :: (Symbolic a, Symbolic (Signed a)) => TypeRep (Signed a)
  BindRep :: (Symbolic a, Symbolic (Bind a)) => TypeRep (Bind a)
  ListRep :: (Symbolic a, Symbolic [a]) => TypeRep [a]
  SeqRep :: (Symbolic a, Symbolic (Seq a)) => TypeRep (Seq a)
  InputRep :: (Symbolic a, Symbolic (Input a)) => TypeRep (Input a)

class Symbolic a where
  typeRep_ :: TypeRep a

typeRep :: Symbolic a => a -> TypeRep a
typeRep _ = typeRep_

-- $(symbolicInstances ''TypeRep ''Symbolic 'typeRep)
instance Symbolic Form where typeRep_ = FormRep
instance Symbolic Clause where typeRep_ = ClauseRep
instance Symbolic Term where typeRep_ = TermRep
instance Symbolic Atomic where typeRep_ = AtomicRep
instance Symbolic a => Symbolic (Signed a) where typeRep_ = SignedRep
instance Symbolic a => Symbolic (Bind a) where typeRep_ = BindRep
instance Symbolic a => Symbolic [a] where typeRep_ = ListRep
instance Symbolic a => Symbolic (Seq a) where typeRep_ = SeqRep
instance Symbolic a => Symbolic (Input a) where typeRep_ = InputRep

-- Unpacking a type
data Unpacked a where
  Const :: a -> Unpacked a
  Unary :: Symbolic a => (a -> b) -> a -> Unpacked b
  Binary :: (Symbolic a, Symbolic b) => (a -> b -> c) -> a -> b -> Unpacked c

class Unpack a where
  unpack' :: a -> Unpacked a

-- This inline declaration is crucial so that
-- pattern-matching on an unpack degenerates into typecase.
{-# INLINE unpack #-}
unpack :: Symbolic a => a -> Unpacked a
unpack x = -- $(mkUnpack ''TypeRep [| unpack' x |] [| typeRep x |])
  case typeRep x of
    FormRep -> unpack' x
    ClauseRep -> unpack' x
    TermRep -> unpack' x
    AtomicRep -> unpack' x
    SignedRep -> unpack' x
    BindRep -> unpack' x
    ListRep -> unpack' x
    SeqRep -> unpack' x
    InputRep -> unpack' x

instance Unpack Form where
  unpack' (Literal l) = Unary Literal l
  unpack' (Not t) = Unary Not t
  unpack' (And ts) = Unary And ts
  unpack' (Or ts) = Unary Or ts
  unpack' (Equiv t u) = Binary Equiv t u
  unpack' (ForAll b) = Unary ForAll b
  unpack' (Exists b) = Unary Exists b

instance Unpack Clause where
  unpack' (Clause ls) = Unary Clause ls

instance Unpack Term where
  unpack' t@Var{} = Const t
  unpack' (f :@: ts) = Unary (f :@:) ts

instance Unpack Atomic where
  unpack' (t :=: u) = Binary (:=:) t u
  unpack' (Tru p) = Unary Tru p

instance Symbolic a => Unpack (Signed a) where
  unpack' (Pos x) = Unary Pos x
  unpack' (Neg x) = Unary Neg x

instance Symbolic a => Unpack (Bind a) where
  unpack' (Bind vs x) = Unary (Bind vs) x

instance Symbolic a => Unpack [a] where
  unpack' [] = Const []
  unpack' (x:xs) = Binary (:) x xs

instance Symbolic a => Unpack (Seq a) where
  unpack' S.Nil = Const S.Nil
  unpack' (S.Unit x) = Unary S.Unit x
  unpack' (S.Append x y) = Binary S.Append x y

instance Symbolic a => Unpack (Input a) where
  unpack' (Input tag kind what) = Unary (Input tag kind) what

----------------------------------------------------------------------
-- Functions operating on symbolic terms

subst :: Symbolic a => Subst -> a -> a
subst s x = C.value x (subst' s x)

subst' :: Symbolic a => Subst -> a -> C.Changing a
subst' s t = aux s (typeRep t) t (unpack t)
  where
    aux s TermRep Var{} _ =
      case NameMap.lookup (name t) s of
        Just (_ ::: u) -> C.changed u
        Nothing -> C.unchanged
    aux s BindRep (Bind vs x) _ = fmap (Bind vs) (subst' (s Map.\\ vs) x)
    aux s _ _ Const{} = C.unchanged
    aux s _ _ (Unary f x) = fmap f (subst' s x)
    aux s _ _ (Binary f x y) = C.lift2 f x (subst' s x) y (subst' s y)

{-# INLINE collect #-}
collect :: forall a b. Symbolic a => (forall a. TypeRep a -> a -> Seq b) -> a -> Seq b
collect f = aux
  where aux :: forall a. Symbolic a => a -> Seq b
        aux x =
          f (typeRep x) x `S.append` 
          case unpack x of
            Const{} -> S.Nil
            Unary _ x -> aux x
            Binary _ x y -> aux x `S.append` aux y

free :: Symbolic a => a -> NameMap Variable
free x = aux (typeRep x) x (unpack x)
  where aux TermRep (Var v) _ = NameMap.singleton v
        aux BindRep (Bind vs x) t = free x Map.\\ vs
        aux _ _ Const{} = Map.empty
        aux _ _ (Unary _ x) = free x
        aux _ _ (Binary _ x y) = free x `Map.union` free y

bind :: Symbolic a => a -> Bind a
bind x = Bind (free x) x

names :: Symbolic a => a -> Seq Name
names = collect f
  where {-# INLINE f #-}
        f :: TypeRep a -> a -> Seq Name
        f TermRep t = S.Unit (name t)
        f BindRep (Bind vs _) = S.fromList (map name (NameMap.toList vs))
        f _ _ = S.Nil

-- uniqueNames :: Symbolic a => a -> NameM a
-- uniqueNames x =
--   let f Nothing = x
--       f (Just (Bind _ x)) = x in
--   let ?lookup = \v s ->
--         case NameMap.lookup (name v) s of
--           Nothing -> fail ""          
--           Just (_ ::: t) -> return t
--       ?bind = \vs s -> do
--         used <- get
--         let (stale, fresh) = partition (`NameMap.member` used) (NameMap.toList vs)
--         stale' <- sequence [ fmap (::: t) (lift (newName x)) | x ::: t <- stale ]
--         put (used `Map.union` NameMap.fromList fresh `Map.union` NameMap.fromList stale')
--         case stale of
--           [] -> return (vs, s)
--           _ -> return (NameMap.fromList (stale' ++ fresh),
--                        NameMap.fromList [name x ::: Var y | (x, y) <- stale `zip` stale'] `Map.union` s)
--   in fmap f (evalStateT (runMaybeT (substM Map.empty (bind x))) Map.empty)
