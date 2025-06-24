-- Formulae, inputs, terms and so on.
--
-- "Show" instances for several of these types are found in TPTP.Print.

{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, Rank2Types, GADTs, TypeOperators, ScopedTypeVariables, BangPatterns, PatternGuards, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Jukebox.Form where

import Prelude hiding (sequence, mapM)
import qualified Data.Set as Set
import Data.Set(Set)
import qualified Data.Map.Strict as Map
import Data.Map(Map)
import Data.Ord
import Jukebox.Name
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Data.List
import Data.Maybe
import Jukebox.Utils
import Data.Typeable(Typeable)
import Data.Monoid
import qualified Data.DList as DList
import Data.DList(DList)
import Data.MemoUgly

-- Set to True to switch on some sanity checks
debugging :: Bool
debugging = False

----------------------------------------------------------------------
-- Types

data Type =
    O
  | Type { tname :: !Name }
  deriving Typeable

indType, intType, ratType, realType :: Type
indType = Type (name "$i")
intType = Type (name "$int")
ratType = Type (name "$rat")
realType = Type (name "$real")

data FunType = FunType { args :: [Type], res :: Type } deriving (Eq, Ord, Typeable)

-- Helper function for defining (Eq, Ord) instances
typeMaybeName :: Type -> Maybe Name
typeMaybeName O = Nothing
typeMaybeName Type{tname = t} = Just t

instance Eq Type where
  t1 == t2 = typeMaybeName t1 == typeMaybeName t2

instance Ord Type where
  compare = comparing typeMaybeName

instance Named Type where
  name O = name "$o"
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
data Term = Var Variable | Function :@: [Term] deriving (Eq, Ord)

instance Named Term where
  name (Var x) = name x
  name (f :@: _) = name f

instance Typed Term where
  typ (Var x) = typ x
  typ (f :@: _) = typ f

newSymbol :: Named a => a -> b -> NameM (Name ::: b)
newSymbol x ty = fmap (::: ty) (newName x)

newFunction :: Named a => a -> [Type] -> Type -> NameM Function
newFunction x args res = newSymbol x (FunType args res)

newType :: Named a => a -> NameM Type
newType x = Type <$> newName x

funArgs :: Function -> [Type]
funArgs (_ ::: ty) = args ty

arity :: Function -> Int
arity = length . funArgs

size :: Term -> Int
size Var{} = 1
size (_f :@: xs) = 1 + sum (map size xs)

subterms :: Term -> [Term]
subterms t =
  t:
  case t of
    Var _ -> []
    _f :@: ts -> concatMap subterms ts

contexts :: Term -> [(Term, Term -> Term)]
contexts t = ctxs t id
  where
    ctxs :: Term -> (Term -> Term) -> [(Term, Term -> Term)]
    ctxs t k =
      (t, k):
      case t of
        Var _ -> []
        f :@: ts ->
          concat
          [ ctxs (ts !! i) (\u -> k (f :@: (take i ts ++ [u] ++ drop (i+1) ts)))
          | i <- [0..length ts-1] ]

----------------------------------------------------------------------
-- Literals

infix 8 :=:
data Atomic = Term :=: Term | Tru Term

-- Helper for (Eq Atomic, Ord Atomic) instances
normAtomic :: Atomic -> Either (Term, Term) Term
normAtomic (t1 :=: t2) | t1 > t2 = Left (t2, t1)
                       | otherwise = Left (t1, t2)
normAtomic (Tru p) = Right p

instance Eq Atomic where
  t1 == t2 = normAtomic t1 == normAtomic t2

instance Ord Atomic where
  compare = comparing normAtomic

data Signed a = Pos a | Neg a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

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

signForm :: Signed a -> Form -> Form
signForm (Pos _) f = f
signForm (Neg _) f = Not f

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
  | And [Form]
  | Or [Form]
  | Equiv Form Form
  | ForAll {-# UNPACK #-} !(Bind Form)
  | Exists {-# UNPACK #-} !(Bind Form)
    -- Just exists so that parsing followed by pretty-printing is
    -- somewhat lossless; the simplify function will get rid of it
  | Connective Connective Form Form
  deriving (Eq, Ord)

-- Miscellaneous connectives that exist in TPTP
data Connective = Implies | Follows | Xor | Nor | Nand
  deriving (Eq, Ord)

connective :: Connective -> Form -> Form -> Form
connective Implies t u = nt t \/ u
connective Follows t u = t \/ nt u
connective Xor t u = nt (t `Equiv` u)
connective Nor t u = nt (t \/ u)
connective Nand t u = nt (t /\ u)

data Bind a = Bind (Set Variable) a
  deriving (Eq, Ord)

true, false :: Form
true = And []
false = Or []

isTrue, isFalse :: Form -> Bool
isTrue (And []) = True
isTrue _ = False
isFalse (Or []) = True
isFalse _ = False

nt :: Form -> Form
nt (Not a) = a
nt a       = Not a

(.=>.) :: Form -> Form -> Form
(.=>.) = connective Implies

(.=.) :: Term -> Term -> Form
t .=. u | typ t == O = Literal (Pos (Tru t)) `Equiv` Literal (Pos (Tru u))
        | otherwise = Literal (Pos (t :=: u))

(/\), (\/) :: Form -> Form -> Form
And as /\ And bs = And (as ++ bs)
a      /\ b | isFalse a || isFalse b = false
And as /\ b      = And (b:as)
a      /\ And bs = And (a:bs)
a      /\ b      = And [a, b]

Or as \/ Or bs = Or (as ++ bs)
a     \/ b | isTrue a || isTrue b = true
Or as \/ b     = Or (b:as)
a     \/ Or bs = Or (a:bs)
a     \/ b     = Or [a, b]

closeForm :: Form -> Form
closeForm f | Set.null vars = f
            | otherwise = ForAll (Bind vars f)
  where vars = free f

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
simplify (And ts) = foldr (/\) true (fmap simplify ts)
simplify (Or ts) = foldr (\/) false (fmap simplify ts)
simplify (Equiv t u) = equiv (simplify t) (simplify u)
  where equiv t u | isTrue t = u
                  | isTrue u = t
                  | isFalse t = nt u
                  | isFalse u = nt t
                  | otherwise = Equiv t u
simplify (ForAll (Bind vs t)) = forAll vs (simplify t)
  where forAll vs t | Set.null vs = t
        forAll vs (ForAll (Bind vs' t)) = ForAll (Bind (Set.union vs vs') t)
        forAll vs t = ForAll (Bind vs t)
simplify (Exists (Bind vs t)) = exists vs (simplify t)
  where exists vs t | Set.null vs = t
        exists vs (Exists (Bind vs' t)) = Exists (Bind (Set.union vs vs') t)
        exists vs t = Exists (Bind vs t)

----------------------------------------------------------------------
-- Clauses

data CNF =
  CNF {
    axioms :: [Input Clause],
    conjectures :: [[Input Clause]],
    satisfiable :: Maybe Model -> Answer,
    unsatisfiable :: Maybe CNFRefutation -> Answer }

toCNF :: [Input Clause] -> [[Input Clause]] -> CNF
toCNF axioms [] = CNF axioms [[]] (Sat Satisfiable) (Unsat Unsatisfiable)
toCNF axioms [conjecture] = CNF axioms [conjecture] (Sat CounterSatisfiable) (Unsat Theorem)
toCNF axioms conjectures = CNF axioms conjectures (\_ -> NoAnswer GaveUp) (Unsat Theorem)

newtype Clause = Clause (Bind [Literal])

clause :: [Literal] -> Clause
clause xs = Clause (bind xs)

toForm :: Clause -> Form
toForm (Clause (Bind vs ls))
  | Set.null vs = Or (map Literal ls)
  | otherwise = ForAll (Bind vs (Or (map Literal ls)))

toLiterals :: Clause -> [Literal]
toLiterals (Clause (Bind _ ls)) = ls

toClause :: Form -> Maybe Clause
toClause (ForAll (Bind _ f)) = toClause f
toClause f = clause <$> cl f
  where
    cl (Or fs) = concat <$> mapM cl fs
    cl (Literal l) = Just [l]
    cl (Not (Literal l)) = Just [neg l]
    cl _ = Nothing

----------------------------------------------------------------------
-- Problems

type Tag = String

data Kind = Ax AxKind | Conj ConjKind deriving (Eq, Ord)
data AxKind =
  Axiom | Hypothesis | Definition | Assumption | Lemma | TheoremKind |
  NegatedConjecture deriving (Eq, Ord)
data ConjKind = Conjecture | Question deriving (Eq, Ord)

data Answer = Sat SatReason (Maybe Model) | Unsat UnsatReason (Maybe CNFRefutation) | NoAnswer NoAnswerReason
  deriving (Eq, Ord)

data NoAnswerReason = GaveUp | Timeout deriving (Eq, Ord, Show)
data SatReason = Satisfiable | CounterSatisfiable deriving (Eq, Ord, Show)
data UnsatReason = Unsatisfiable | Theorem deriving (Eq, Ord, Show)
type Model = [String]
type CNFRefutation = [String]

instance Show Answer where
  show (Sat reason _) = show reason
  show (Unsat reason _) = show reason
  show (NoAnswer x) = show x

explainAnswer :: Answer -> String
explainAnswer (Sat Satisfiable _) = "the axioms are consistent"
explainAnswer (Sat CounterSatisfiable _) = "the conjecture is false"
explainAnswer (Unsat Unsatisfiable _) = "the axioms are contradictory"
explainAnswer (Unsat Theorem _) = "the conjecture is true"
explainAnswer (NoAnswer GaveUp) = "couldn't solve the problem"
explainAnswer (NoAnswer Timeout) = "ran out of time while solving the problem"

answerSZS :: Answer -> [String]
answerSZS answer =
  ["% SZS status " ++ show answer] ++
  case answerJustification answer of
    Nothing -> []
    Just strs -> [""] ++ strs

answerJustification :: Answer -> Maybe [String]
answerJustification (Sat _ (Just model)) =
  Just $
    ["% SZS output start Model"] ++
    model ++
    ["% SZS output end Model"]
answerJustification (Unsat _ (Just refutation)) =
  Just $
    ["% SZS output start CNFRefutation"] ++
    refutation ++
    ["% SZS output end CNFRefutation"]
answerJustification _ = Nothing

data Input a = Input
  { ident  :: Maybe Name,
    tag    :: Tag,
    kind   :: Kind,
    source :: InputSource,
    what   :: a }
  deriving (Functor, Foldable, Traversable)

data InputSource =
    Unknown
  | FromFile String Int
  | Inference String String [InputPlus Form]

inference :: String -> String -> [Input Form] -> InputSource
inference name status parents = Inference name status (map inputPlus parents)

data InputPlus a = InputPlus
  { inputNames     :: [Name],
    inputFunctions :: [Function],
    inputTypes     :: [Type],
    inputValue     :: Input a }

inputPlus :: Symbolic a => Input a -> InputPlus a
inputPlus x =
  InputPlus {
    inputNames = names x,
    inputFunctions = functions x,
    inputTypes = types' x,
    inputValue = x }

type Problem a = [Input a]

----------------------------------------------------------------------
-- Symbolic stuff

-- A universe of types with typecase
data TypeOf a where
  Form :: TypeOf Form
  Clause_ :: TypeOf Clause
  Term :: TypeOf Term
  Atomic :: TypeOf Atomic
  Signed :: (Symbolic a, Symbolic (Signed a)) => TypeOf (Signed a)
  Bind_ :: (Symbolic a, Symbolic (Bind a)) => TypeOf (Bind a)
  List :: (Symbolic a, Symbolic [a]) => TypeOf [a]
  Input_ :: (Symbolic a, Symbolic (Input a)) => TypeOf (Input a)
  CNF_ :: TypeOf CNF

class Symbolic a where
  typeOf :: a -> TypeOf a

instance Symbolic Form where typeOf _ = Form
instance Symbolic Clause where typeOf _ = Clause_
instance Symbolic Term where typeOf _ = Term
instance Symbolic Atomic where typeOf _ = Atomic
instance Symbolic a => Symbolic (Signed a) where typeOf _ = Signed
instance Symbolic a => Symbolic (Bind a) where typeOf _ = Bind_
instance Symbolic a => Symbolic [a] where typeOf _ = List
instance Symbolic a => Symbolic (Input a) where typeOf _ = Input_
instance Symbolic CNF where typeOf _ = CNF_

-- Generic representations of values.
data Rep a where
  Const :: !a -> Rep a
  Unary :: Symbolic a => (a -> b) -> a -> Rep b
  Binary :: (Symbolic a, Symbolic b) => (a -> b -> c) -> a -> b -> Rep c

-- This inline declaration is crucial so that
-- pattern-matching on a rep degenerates into typecase.
{-# INLINE rep #-}
rep :: Symbolic a => a -> Rep a
rep x =
  case typeOf x of
    Form -> rep' x
    Clause_ -> rep' x
    Term -> rep' x
    Atomic -> rep' x
    Signed -> rep' x
    Bind_ -> rep' x
    List -> rep' x
    Input_ -> rep' x
    CNF_ -> rep' x

-- Implementation of rep for all types
class Unpack a where
  rep' :: a -> Rep a

instance Unpack Form where
  rep' (Literal l) = Unary Literal l
  rep' (Not t) = Unary Not t
  rep' (And ts) = Unary And ts
  rep' (Or ts) = Unary Or ts
  rep' (Equiv t u) = Binary Equiv t u
  rep' (ForAll b) = Unary ForAll b
  rep' (Exists b) = Unary Exists b
  rep' (Connective c t u) = Binary (Connective c) t u

instance Unpack Clause where
  rep' (Clause ls) = Unary Clause ls

instance Unpack Term where
  rep' t@Var{} = Const t
  rep' (f :@: ts) = Unary (f :@:) ts

instance Unpack Atomic where
  rep' (t :=: u) = Binary (:=:) t u
  rep' (Tru p) = Unary Tru p

instance Symbolic a => Unpack (Signed a) where
  rep' (Pos x) = Unary Pos x
  rep' (Neg x) = Unary Neg x

instance Symbolic a => Unpack (Bind a) where
  rep' (Bind vs x) = Unary (Bind vs) x

instance Symbolic a => Unpack [a] where
  rep' [] = Const []
  rep' (x:xs) = Binary (:) x xs

instance Symbolic a => Unpack (Input a) where
  rep' (Input ident tag kind info what) = Unary (Input ident tag kind info) what

instance Unpack CNF where
  rep' (CNF ax conj s1 s2) =
    Binary (\ax' conj' -> CNF ax' conj' s1 s2) ax conj

-- Little generic strategies

{-# INLINE recursively #-}
recursively :: Symbolic a => (forall a. Symbolic a => a -> a) -> a -> a
recursively h t =
  case rep t of
    Const x -> x
    Unary f x -> f (h x)
    Binary f x y -> f (h x) (h y)

{-# INLINE recursivelyM #-}
recursivelyM :: (Monad m, Symbolic a) => (forall a. Symbolic a => a -> m a) -> a -> m a
recursivelyM h t =
  case rep t of
    Const x -> return x
    Unary f x -> liftM f (h x)
    Binary f x y -> liftM2 f (h x) (h y)

{-# INLINE collect #-}
collect :: (Symbolic a, Monoid b) => (forall a. Symbolic a => a -> b) -> a -> b
collect h t =
  case rep t of
    Const _x -> mempty
    Unary _f x -> h x
    Binary _f x y -> h x `mappend` h y

----------------------------------------------------------------------
-- Substitutions

type Subst = Map Variable Term

ids :: Subst
ids = Map.empty

(|=>) :: Variable -> Term -> Subst
v |=> x = Map.singleton v x

(|+|) :: Subst -> Subst -> Subst
(|+|) = Map.union

subst :: Symbolic a => Subst -> a -> a
subst s t =
  case typeOf t of
    Term -> term t
    Bind_ -> bind t
    _ -> generic t
  where
    term (Var x)
      | Just u <- Map.lookup x s = u
    term t = generic t

    bind :: Symbolic a => Bind a -> Bind a
    bind (Bind vs t) =
      Bind vs (subst (checkBinder vs (s Map.\\ vs')) t)
      where
        vs' = Map.fromSet (const ()) vs

    generic :: Symbolic a => a -> a
    generic t = recursively (subst s) t

match :: Term -> Term -> Maybe Subst
match pat t = execStateT (matchM pat t) ids
  where
    matchM (Var x) t = do
      sub <- get
      case Map.lookup x sub of
        Nothing -> put (sub |+| (x |=> t))
        Just u | u == t -> return ()
        _ -> mzero
    matchM (f :@: ts) (g :@: us) | f == g =
      zipWithM_ matchM ts us
    matchM _ _ = mzero

----------------------------------------------------------------------
-- Functions operating on symbolic terms

free :: Symbolic a => a -> Set Variable
free t
  | Term <- typeOf t,
    Var x <- t        = var x
  | Bind_ <- typeOf t = bind t
  | otherwise         = collect free t
  where
    var :: Variable -> Set Variable
    var x = Set.singleton x

    bind :: Symbolic a => Bind a -> Set Variable
    bind (Bind vs t) = free t Set.\\ vs

ground :: Symbolic a => a -> Bool
ground = Set.null . free

bind :: Symbolic a => a -> Bind a
bind x = Bind (free x) x

-- Helper function for collecting information from terms and binders.
termsAndBinders :: forall a b.
                   Symbolic a =>
                   (Term -> DList b) ->
                   (forall a. Symbolic a => Bind a -> [b]) ->
                   (forall a. Symbolic a => Input a -> [b]) ->
                   a -> [b]
termsAndBinders term bind inp = DList.toList . aux where
  aux :: Symbolic c => c -> DList b
  aux t =
    collect aux t `mplus`
    case typeOf t of
      Term -> term t
      Bind_ -> DList.fromList (bind t)
      Input_ -> DList.fromList (inp t)
      _ -> mzero

names :: Symbolic a => a -> [Name]
names = usort . termsAndBinders term bind inp where
  term t = DList.fromList (allNames t) `mappend` DList.fromList (allNames (typ t))

  bind :: Symbolic a => Bind a -> [Name]
  bind (Bind vs _) = map name (Set.toList vs)

  inp :: Symbolic a => Input a -> [Name]
  inp (Input ident _ _ source _) =
    maybeToList ident ++
    case source of
      Inference _ _ inps ->
        concatMap inputNames inps
      _ -> []

run :: Symbolic a => a -> (a -> NameM b) -> b
run x f = runNameM (names x) (f x)

run_ :: Symbolic a => a -> NameM b -> b
run_ x mx = run x (const mx)

types :: Symbolic a => a -> [Type]
types = usort . termsAndBinders term bind inp where
  term t = return (typ t)

  bind :: Symbolic a => Bind a -> [Type]
  bind (Bind vs _) = map typ (Set.toList vs)

  inp :: Symbolic a => Input a -> [Type]
  inp (Input _ _ _ source _) =
    case source of
      Inference _ _ inps ->
        concatMap inputTypes inps
      _ -> []

types' :: Symbolic a => a -> [Type]
types' = filter (/= O) . types

terms :: Symbolic a => a -> [Term]
terms = usort . termsAndBinders term mempty mempty where
  term t = return t

vars :: Symbolic a => a -> [Variable]
vars = usort . termsAndBinders term bind mempty where
  term (Var x) = return x
  term _ = mempty

  bind :: Symbolic a => Bind a -> [Variable]
  bind (Bind vs _) = Set.toList vs

functions :: Symbolic a => a -> [Function]
functions = usort . termsAndBinders term mempty inp where
  term (f :@: _) = return f
  term _ = mempty

  inp :: Symbolic a => Input a -> [Function]
  inp (Input _ _ _ source _) =
    case source of
      Inference _ _ inps ->
        concatMap inputFunctions inps
      _ -> []

funOcc :: Symbolic a => Function -> a -> Int
funOcc f x = getSum (occ x)
  where
    occ :: Symbolic a => a -> Sum Int
    occ x = collect occ x `mappend` occ1 x

    occ1 :: Symbolic a => a -> Sum Int
    occ1 x
      | Term <- typeOf x,
        g :@: _ <- x,
        f == g = Sum 1
      | otherwise = mempty

funsOcc :: Symbolic a => a -> Map Function Int
funsOcc =
  Map.fromList . map f . group . sort . termsAndBinders term mempty mempty
  where
    term (f :@: _) = return f
    term _ = mempty

    f xs@(x:_) = (x, length xs)

isFof :: Symbolic a => a -> Bool
isFof f = length (types' f) <= 1

eraseTypes :: Symbolic a => a -> a
eraseTypes x =
  mapType (\ty -> if ty == O then ty else indType) x

uniqueNames :: Symbolic a => a -> NameM a
uniqueNames t = evalStateT (aux Map.empty t) (Map.fromList [(x, t) | x ::: t <- Set.toList (free t)])
  where aux :: Symbolic a => Subst -> a -> StateT (Map Name Type) NameM a
        aux s t =
          case typeOf t of
            Term -> term s t
            Bind_ -> bind s t
            _ -> generic s t

        term :: Subst -> Term -> StateT (Map Name Type) NameM Term
        term s t@(Var x) = do
          case Map.lookup x s of
            Nothing -> return t
            Just u -> return u
        term s t = generic s t

        bind :: Symbolic a => Subst -> Bind a -> StateT (Map Name Type) NameM (Bind a)
        bind s (Bind vs x) = do
          used <- get
          let (stale, fresh) = partition ((`Map.member` used) . lhs) (Set.toList vs)
              tuple (x ::: y) = (x, y)
          stale' <- sequence [ lift (newSymbol x t) | x ::: t <- stale ]
          put (used `Map.union` Map.fromList (map tuple (fresh ++ stale')))
          case stale of
            [] -> fmap (Bind vs) (aux s x)
            _ ->
              do
                let s' = Map.fromList [(x, Var y) | (x, y) <- stale `zip` stale'] `Map.union` s
                    vs' = Set.fromList (stale' ++ fresh)
                fmap (Bind vs') (aux s' x)

        generic :: Symbolic a => Subst -> a -> StateT (Map Name Type) NameM a
        generic s t = recursivelyM (aux s) t

-- Force a value.
force :: Symbolic a => a -> a
force x = rnf x `seq` x
  where rnf :: Symbolic a => a -> ()
        rnf x =
          case rep x of
            Const !_ -> ()
            Unary _ x -> rnf x
            Binary _ x y -> rnf x `seq` rnf y

-- Check that there aren't two nested binders binding the same variable
check :: Symbolic a => a -> a
check x | not debugging = x
        | check' (free x) x = x
        | otherwise = error "Form.check: invariant broken"
  where check' :: Symbolic a => Set Variable -> a -> Bool
        check' vars t =
          case typeOf t of
            Term -> term vars t
            Bind_ -> bind vars t
            _ -> generic vars t

        term :: Set Variable -> Term -> Bool
        term vars (Var x) = x `Set.member` vars
        term vars t = generic vars t

        bind :: Symbolic a => Set Variable -> Bind a -> Bool
        bind vars (Bind vs t) =
          Set.null (vs `Set.intersection` vars) &&
          check' (vs `Set.union` vars) t

        generic :: Symbolic a => Set Variable -> a -> Bool
        generic vars = getAll . collect (All . check' vars)

-- Check that a binder doesn't capture variables from a substitution.
checkBinder :: Set Variable -> Subst -> Subst
checkBinder vs s | not debugging = s
                 | Set.null (free (Map.elems s) `Set.intersection` vs) = s
                 | otherwise = error "Form.checkBinder: capturing substitution"

-- Apply a function to each name, while preserving sharing.
mapName :: Symbolic a => (Name -> Name) -> a -> a
mapName f0 = rename
  where
    rename :: Symbolic a => a -> a
    rename t =
      case typeOf t of
        Term -> term t
        Bind_ -> bind t
        Input_ -> input t
        _ -> recursively rename t

    bind :: Symbolic a => Bind a -> Bind a
    bind (Bind vs t) =  Bind (Set.map var vs) (rename t)
    term (f :@: ts) = fun f :@: map term ts
    term (Var x) = Var (var x)

    input :: Symbolic a => Input a -> Input a
    input (Input id name kind source what) =
      Input (fmap f id) name kind source' (rename what)
      where
        source' =
          case source of
            Inference inf status forms ->
              Inference inf status (map inputPlus forms)
            _ -> source

    inputPlus  :: InputPlus Form -> InputPlus Form
    inputPlus inp =
      InputPlus {
        inputNames = map f (inputNames inp),
        inputFunctions = map fun (inputFunctions inp),
        inputTypes = map type_ (inputTypes inp),
        inputValue = input (inputValue inp) }

    var = memo $ \(x ::: ty) -> f x ::: type_ ty
    fun = memo $ \(x ::: FunType args res) ->
                   f x ::: FunType (map type_ args) (type_ res)
    type_ =
      memo $ \ty ->
        case ty of
          O -> O
          Type name -> Type (f name)

    f = memo f0

-- Apply a function to each type, while preserving sharing.
mapType :: Symbolic a => (Type -> Type) -> a -> a
mapType f0 = mapType'
  where mapType' :: Symbolic a => a -> a
        mapType' t =
          case typeOf t of
            Term -> term t
            Bind_ -> bind t
            _ -> recursively mapType' t

        bind :: Symbolic a => Bind a -> Bind a
        bind (Bind vs t) = Bind (Set.map var vs) (mapType' t)

        term (f :@: ts) = fun f :@: map term ts
        term (Var x) = Var (var x)

        var = memo $ \(x ::: ty) -> x ::: f ty
        fun = memo $ \(x ::: FunType args res) ->
                       x ::: FunType (map f args) (f res)

        f = memo f0
