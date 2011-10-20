-- Formulae, inputs, terms and so on.
--
-- "Show" instances for several of these types are found in TPTP.Print.

{-# LANGUAGE DeriveDataTypeable, TemplateHaskell, FlexibleContexts, Rank2Types, GADTs, TypeOperators, ScopedTypeVariables, BangPatterns #-}
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
import Control.Monad.State.Strict
import Data.List hiding (nub)
import Utils
import Data.DeriveTH
import Data.Derive.Hashable
import Data.Typeable(Typeable)

-- Set to True to switch on some sanity checks
debugging :: Bool
debugging = False

----------------------------------------------------------------------
-- Types

data DomainSize = Finite Int | Infinite deriving (Eq, Ord, Show, Typeable)

data Type =
    O
  | Type {
      tname :: {-# UNPACK #-} !Name,
      -- type is monotone when domain size is >= tmonotone
      tmonotone :: DomainSize,
      -- if there is a model of size >= tsize then there is a model of size tsize
      tsize :: DomainSize,
      -- two types in the same class have to have the same size
      tclass :: Int } deriving Typeable

data FunType = FunType { args :: [Type], res :: !Type } deriving (Eq, Typeable)

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

instance Typed b => Typed (a ::: b) where
  typ (_ ::: t) = typ t

----------------------------------------------------------------------
-- Terms

type Variable = Name ::: Type
type Function = Name ::: FunType
data Term = Var !Variable | !Function :@: [Term] deriving (Eq, Ord)
$(derive makeHashable ''Term)

instance Named Term where
  name (Var x) = name x
  name (f :@: _) = name f

instance Typed Term where
  typ (Var x) = typ x
  typ (f :@: _) = typ f

----------------------------------------------------------------------
-- Literals

data Atomic = !Term :=: !Term | Tru !Term

-- Helper for (Eq Atomic, Ord Atomic, Hashable Atomic) instances
normAtomic :: Atomic -> Either (Term, Term) Term
normAtomic (t1 :=: t2) | t1 > t2 = Left (t2, t1)
                       | otherwise = Left (t1, t2)
normAtomic (Tru p) = Right p

instance Eq Atomic where
  t1 == t2 = normAtomic t1 == normAtomic t2

instance Ord Atomic where
  compare = comparing normAtomic

instance Hashable Atomic where
  hashWithSalt s = hashWithSalt s . normAtomic

data Signed a = Pos !a | Neg !a deriving (Show, Eq, Ord)
$(derive makeHashable ''Signed)

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

-- Invariant: each name is bound only once on each path
-- i.e. nested quantification of the same variable twice is not allowed
-- Not OK: ![X]: (... ![X]: ...)
-- OK:     (![X]: ...) & (![X]: ...)
-- Free variables must also not be bound inside subformulae
data Form
  = Literal Literal
  | Not Form
  | And (Seq Form)
  | Or (Seq Form)
  | Equiv Form Form
  | ForAll (Bind Form)
  | Exists (Bind Form)
    -- Just exists so that parsing followed by pretty-printing is
    -- somewhat lossless; the simplify function will get rid of it
  | Connective Connective Form Form

-- Miscellaneous connectives that exist in TPTP
data Connective = Implies | Follows | Xor | Nor | Nand

connective :: Connective -> Form -> Form -> Form
connective Implies t u = nt t \/ u
connective Follows t u = t \/ nt u
connective Xor t u = nt (t `Equiv` u)
connective Nor t u = nt (t \/ u)
connective Nand t u = nt (t /\ u)

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
(.=>) = connective Implies

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

-- remove Not from the root of a problem
positive :: Form -> Form
positive (Not f) = notInwards f
-- Some connectives are fairly not-ish
positive (Connective c t u)         = positive (connective c t u)
positive f = f

notInwards :: Form -> Form
notInwards (And as)             = Or (fmap notInwards as)
notInwards (Or as)              = And (fmap notInwards as)
notInwards (a `Equiv` b)        = notInwards a `Equiv` b
notInwards (Not a)              = positive a
notInwards (ForAll (Bind vs a)) = Exists (Bind vs (notInwards a))
notInwards (Exists (Bind vs a)) = ForAll (Bind vs (notInwards a))
notInwards (Literal l)          = Literal (neg l)
notInwards (Connective c t u)   = notInwards (connective c t u)

-- remove Exists and Or from the top level of a formula
simple :: Form -> Form
simple (Or as)              = Not (And (fmap nt as))
simple (Exists (Bind vs a)) = Not (ForAll (Bind vs (nt a)))
simple (Connective c t u)   = simple (connective c t u)
simple a                    = a

-- perform some easy algebraic simplifications
simplify t@Literal{} = t
simplify (Connective c t u) = simplify (connective c t u)
simplify (Not t) = simplify (notInwards t)
simplify (And ts) = S.fold (/\) id true (fmap simplify ts)
simplify (Or ts) = S.fold (\/) id false (fmap simplify ts)
simplify (Equiv t u) = equiv (simplify t) (simplify u)
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

type CNF = Closed ([Input Clause], [[Input Clause]])
newtype Clause = Clause (Bind [Literal])

clause :: S.List f => f (Signed Atomic) -> Clause
clause xs = Clause (bind (S.toList xs))

toForm :: Clause -> Form
toForm (Clause (Bind vs ls)) = ForAll (Bind vs (Or (S.fromList (map Literal ls))))

toLiterals :: Clause -> [Literal]
toLiterals (Clause (Bind _ ls)) = ls

----------------------------------------------------------------------
-- Problems

type Tag = BS.ByteString

data Kind = Axiom | Conjecture | Question deriving (Eq, Ord)

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
  Const :: !a -> Unpacked a
  Unary :: Symbolic a => (a -> b) -> a -> Unpacked b
  Binary :: (Symbolic a, Symbolic b) => (a -> b -> c) -> a -> b -> Unpacked c

class Unpack a where
  unpack' :: a -> Unpacked a

-- This inline declaration is crucial so that
-- pattern-matching on an unpack degenerates into typecase.
{-# INLINE unpack #-}
unpack :: Symbolic a => a -> Unpacked a
unpack x = unpackRep (typeRep x) x -- $(mkUnpack ''TypeRep [| unpack' x |] [| typeRep x |])

{-# INLINE unpackRep #-}
unpackRep :: TypeRep a -> a -> Unpacked a
unpackRep FormRep = unpack'
unpackRep ClauseRep = unpack'
unpackRep TermRep = unpack'
unpackRep AtomicRep = unpack'
unpackRep SignedRep = unpack'
unpackRep BindRep = unpack'
unpackRep ListRep = unpack'
unpackRep SeqRep = unpack'
unpackRep InputRep = unpack'

instance Unpack Form where
  unpack' (Literal l) = Unary Literal l
  unpack' (Not t) = Unary Not t
  unpack' (And ts) = Unary And ts
  unpack' (Or ts) = Unary Or ts
  unpack' (Equiv t u) = Binary Equiv t u
  unpack' (ForAll b) = Unary ForAll b
  unpack' (Exists b) = Unary Exists b
  unpack' (Connective c t u) = Binary (Connective c) t u

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
subst s t = aux s (typeRep t) t (unpack t)
  where
    aux s TermRep Var{} _ =
      case NameMap.lookup (name t) s of
        Just (_ ::: u) -> u
        Nothing -> t
    aux s BindRep (Bind vs x) _ = Bind vs (subst (checkBinder vs (s Map.\\ vs)) x)
    aux s _ _ Const{} = t
    aux s _ _ (Unary f x) = f (subst s x)
    aux s _ _ (Binary f x y) = f (subst s x) (subst s y)

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

names :: Symbolic a => a -> [Name]
names = nub . collect f
  where {-# INLINE f #-}
        f :: TypeRep a -> a -> Seq Name
        f TermRep t = S.Unit (name t) `S.append` S.Unit (name (typ t))
        f BindRep (Bind vs _) = S.fromList (map name (NameMap.toList vs))
        f _ _ = S.Nil

types :: Symbolic a => a -> [Type]
types = nub . collect f
  where {-# INLINE f #-}
        f :: TypeRep a -> a -> Seq Type
        f TermRep t = S.Unit (typ t)
        f BindRep (Bind vs _) = S.fromList (map typ (NameMap.toList vs))
        f _ _ = S.Nil

vars :: Symbolic a => a -> [Variable]
vars = nub . collect f
  where {-# INLINE f #-}
        f :: TypeRep a -> a -> Seq Variable
        f TermRep (Var x) = S.Unit x
        f BindRep (Bind vs _) = S.fromList (NameMap.toList vs)
        f _ _ = S.Nil

functions :: Symbolic a => a -> [Function]
functions = nub . collect f
  where {-# INLINE f #-}
        f :: TypeRep a -> a -> Seq Function
        f TermRep (f :@: _) = S.Unit f
        f _ _ = S.Nil

isFof :: Symbolic a => a -> Bool
isFof f = all fof (functions f) && all (`elem` open stdNames) (map name (types f))
  where fof (_ ::: FunType args res) =
          and [ name (typ arg) == nameI | arg <- args ] &&
            name res `elem` [nameI, nameO]

uniqueNames :: Symbolic a => a -> NameM a
uniqueNames x = evalStateT (aux Map.empty x) (free x)
  where aux :: Symbolic a => Subst -> a -> StateT (NameMap Variable) NameM a
        aux s x = aux' s (typeRep x) x
        aux' :: Subst -> TypeRep a -> a -> StateT (NameMap Variable) NameM a
        aux' s TermRep t@(Var v) = do
          case NameMap.lookup (name v) s of
            Nothing -> return t
            Just (_ ::: t) -> return t
        aux' s BindRep (Bind vs x) = do
          used <- get
          let (stale, fresh) = partition (`NameMap.member` used) (NameMap.toList vs)
          stale' <- sequence [ fmap (::: t) (lift (newName x)) | x ::: t <- stale ]
          put (used `Map.union` NameMap.fromList fresh `Map.union` NameMap.fromList stale')
          case stale of
            [] -> fmap (Bind vs) (aux s x)
            _ ->
              do
                let s' = NameMap.fromList [name x ::: Var y | (x, y) <- stale `zip` stale'] `Map.union` s
                    vs' = NameMap.fromList (stale' ++ fresh)
                fmap (Bind vs') (aux s' x)
        aux' s r t =
          case unpackRep r t of
           Const{} -> return t
           Unary f x -> fmap f (aux s x)
           Binary f x y -> liftM2 f (aux s x) (aux s y)

-- Force a value.
force :: Symbolic a => a -> a
force x = aux x `seq` x
  where aux :: Symbolic a => a -> ()
        aux x =
          case unpack x of
            Const !_ -> ()
            Unary _ x -> aux x
            Binary _ x y -> aux x `seq` aux y

-- Check that there aren't two nested binders binding the same variable
check :: Symbolic a => a -> a
check x | not debugging = x
        | aux (free x) x = x
        | otherwise = error "Form.check: invariant broken"
  where aux :: Symbolic a => NameMap Variable -> a -> Bool
        aux vars x = aux' vars (typeRep x) x (unpack x)
        aux' :: NameMap Variable -> TypeRep a -> a -> Unpacked a -> Bool
        aux' vars TermRep (Var v) _ = v `NameMap.member` vars
        aux' vars BindRep (Bind vs t) _ =
          Map.null (vs `Map.intersection` vars) &&
          aux (vs `Map.union` vars) t
        aux' vars _ _ Const{} = True
        aux' vars _ _ (Unary _ x) = aux vars x
        aux' vars _ _ (Binary _ x y) = aux vars x && aux vars y

-- Check that a binder doesn't capture variables from a substitution.
checkBinder :: NameMap Variable -> Subst -> Subst
checkBinder vs s | not debugging = s
                 | Map.null (free [ t | _ ::: t <- NameMap.toList s ] `Map.intersection` vs) = s
                 | otherwise = error "Form.checkBinder: capturing substitution"

-- Apply a function to each type, while preserving sharing.
mapType :: Symbolic a => (Type -> Type) -> a -> a
mapType f x = aux x
  where typeMap :: NameMap (Type ::: Type)
        typeMap = NameMap.fromList [ ty ::: f ty | ty <- types x ]
        lookupType = typ . flip NameMap.lookup_ typeMap
        varMap :: NameMap Variable
        varMap = NameMap.fromList [ n ::: lookupType ty | n ::: ty <- vars x ]
        funMap :: NameMap Function
        funMap = NameMap.fromList [ n ::: FunType (map lookupType args)
                                                  (lookupType res)
                                  | n ::: FunType args res <- functions x ]

        aux :: Symbolic a => a -> a
        aux x =
          case (typeRep x, x, unpack x) of
            (BindRep, Bind vs t, _) ->
              -- keys of binder don't change
              Bind (fmap (flip NameMap.lookup_ varMap) vs) (aux t)
            (TermRep, Var x, _) -> Var (NameMap.lookup_ x varMap)
            (TermRep, f :@: ts, _) -> NameMap.lookup_ f funMap :@: map aux ts
            (_, _, Const _) -> x
            (_, _, Unary f x) -> f (aux x)
            (_, _, Binary f x y) -> f (aux x) (aux y)
