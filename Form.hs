{-# LANGUAGE TypeOperators, ImplicitParams #-}
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
import Control.Monad.Trans
import Control.Monad.Identity
import Control.Monad.Maybe
import Control.Monad.Writer
import Data.Maybe

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

simple :: Form -> Form
simple (Or as)              = Not (And (fmap nt as))
simple (Exists (Bind vs a)) = Not (ForAll (Bind vs (nt a)))
simple a                    = a

type Subst = NameMap (Name ::: Term)

ids :: Subst
ids = Map.empty

(|=>) :: Named a => a -> Term -> Subst
v |=> x = NameMap.singleton (name v ::: x)

(|+|) :: Subst -> Subst -> Subst
(|+|) = Map.union

type Clause = [Signed Atomic]

bind :: Symbolic a => a -> Bind a
bind x = Bind (free x) x

toForm :: Bind Clause -> Form
toForm (Bind xs ls) = ForAll (Bind xs (And (S.fromList (map Literal ls))))

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
  things :: (Variable -> Seq b) -> (Term -> Seq b) -> a -> Seq b
  substM ::
    (Monad m,
     ?lookup :: Variable -> s -> MaybeT m Term,
     ?bind :: NameMap Variable -> s -> s) =>
    s -> a -> MaybeT m a

subterms :: Symbolic a => a -> Seq Term
subterms = things (const S.Nil) S.Unit

free :: Symbolic a => a -> NameMap Variable
free x =
  let ?lookup = \v _ -> do { tell (NameMap.singleton v); fail "" }
      ?bind = \_ -> id
  in execWriterT (runMaybeT (substM () x)) Map.empty

subst :: Symbolic a => Subst -> a -> a
subst s x =
  let ?lookup = \v s ->
        case NameMap.lookup (name v) s of
          Nothing -> fail ""
          Just (_ ::: t) -> return t
      ?bind = \vs s -> s Map.\\ vs
  in fromMaybe x (runIdentity (runMaybeT (substM s x)))

vars :: Symbolic a => a -> Seq Variable
vars = things S.Unit f
  where f (Var x) = S.Unit x
        f _ = S.Nil

functions :: Symbolic a => a -> Seq Function
functions = things (const S.Nil) f
  where f (x :@: _) = S.Unit x
        f _ = S.Nil

types :: Symbolic a => a -> Seq Type
types = things (S.Unit . typ) (S.Unit . typ)

names :: Symbolic a => a -> Seq Name
names = things f f
  where f :: (Named a, Typed a) => a -> Seq Name
        f x = S.Unit (name x) `S.append` S.Unit (name (typ x))

instance Symbolic Form where
  things f g (Literal l) = things f g l
  things f g (Not t) = things f g t
  things f g (And xs) = things f g xs
  things f g (Or xs) = things f g xs
  things f g (Equiv t u) = things f g (t, u)
  things f g (ForAll t) = things f g t
  things f g (Exists t) = things f g t

  substM s (Literal l) = liftM Literal (substM s l)
  substM s (Not t) = liftM Not (substM s t)
  substM s (And xs) = liftM And (substM s xs)
  substM s (Or xs) = liftM Or (substM s xs)
  substM s (Equiv t u) = liftM (uncurry Equiv) (substM s (t, u))
  substM s (ForAll t) = liftM ForAll (substM s t)
  substM s (Exists t) = liftM Exists (substM s t)

instance Symbolic a => Symbolic (Bind a) where
  things f g (Bind vs x) = S.concat (map f (NameMap.toList vs)) `S.append` things f g x
  substM s (Bind vs x) = liftM (Bind vs) (substM (?bind vs s) x)

instance Symbolic a => Symbolic (Signed a) where
  things f g (Pos x) = things f g x
  things f g (Neg x) = things f g x
  
  substM s (Pos x) = liftM Pos (substM s x)
  substM s (Neg x) = liftM Neg (substM s x)

instance Symbolic Atomic where
  things f g (t :=: u) = things f g (t, u)
  substM s (t :=: u) = liftM (uncurry (:=:)) (substM s (t, u))

instance Symbolic Term where
  things f g t@Var{} = g t
  things f g t@(_ :@: ts) = g t `S.append` S.concat (fmap (things f g) ts)
  
  substM s t@(Var v) = ?lookup v s
  substM s (f :@: ts) = liftM (f :@:) (substM s ts)

instance Symbolic a => Symbolic (Input a) where
  things f g = things f g . what
  substM s (Input tag kind what) = liftM (Input tag kind) (substM s what)
  
instance Symbolic a => Symbolic [a] where
  things f g = things f g . S.fromList
  substM s [] = return []
  substM s (x:xs) = liftM (uncurry (:)) (substM s (x, xs))

instance Symbolic a => Symbolic (Seq a) where
  things f g = S.concat . fmap (things f g)
  substM s S.Nil = return S.Nil
  substM s (S.Unit x) = liftM S.Unit (substM s x)
  substM s (S.Append x y) = liftM (uncurry S.Append) (substM s (x, y))
  
instance (Symbolic a, Symbolic b) => Symbolic (a, b) where
  things f g (x, y) = things f g x `S.append` things f g y
  substM s (x, y) = do
    x' <- lift (runMaybeT (substM s x))
    y' <- lift (runMaybeT (substM s y))
    case (x', y') of
      (Nothing, Nothing) -> fail ""
      _ -> return (fromMaybe x x', fromMaybe y y')

uniqueNames :: Form -> NameM Form
uniqueNames = undefined
