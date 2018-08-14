{-# LANGUAGE TypeOperators, GeneralizedNewtypeDeriving, FlexibleInstances, CPP #-}
module Jukebox.Name where

import Control.Monad
import Control.Monad.Trans.State.Strict
import Data.Ord
import Data.Int
import Data.Symbol
import Data.Char
import Data.Ratio
#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif

data Name =
    Fixed !FixedName (Maybe String)
  | Unique {-# UNPACK #-} !Int64 String (Maybe String) Renamer
  | Variant !Name ![Name] Renamer

data FixedName =
    Basic {-# UNPACK #-} !Symbol
  | Overloaded {-# UNPACK #-} !Symbol {-# UNPACK #-} !Symbol
  | Integer !Integer
  | Rational !Rational
  | Real !Rational
  deriving (Eq, Ord)

type Renamer = String -> Int -> Renaming
data Renaming = Renaming [String] String

base :: Named a => a -> String
base x =
  case name x of
    Fixed x _ -> show x
    Unique _ xs _ _ -> xs
    Variant x _ _ -> base x

label :: Named a => a -> Maybe String
label x =
  case name x of
    Fixed _ x -> x
    Unique _ _ x _ -> x
    Variant x _ _ -> label x

hasLabel :: Named a => String -> a -> Bool
hasLabel l x = label x == Just l

withMaybeLabel :: Maybe String -> Name -> Name
withMaybeLabel l (Fixed x _) = Fixed x l
withMaybeLabel l (Unique x xs _ f) = Unique x xs l f
withMaybeLabel l (Variant x xs r) = Variant (withMaybeLabel l x) xs r

withLabel :: String -> Name -> Name
withLabel l x = withMaybeLabel (Just l) x

instance Show FixedName where
  show (Basic xs) = unintern xs
  show (Overloaded xs _) = unintern xs
  show (Integer n) = show n
  show (Rational x) = show (numerator x) ++ "/" ++ show (denominator x)
  show (Real x) = "$to_real(" ++ show (numerator x) ++ "/" ++ show (denominator x) ++ ")"

renamer :: Named a => a -> Renamer
renamer x =
  case name x of
    Fixed _ _ -> defaultRenamer
    Unique _ _ _ f -> f
    Variant _ _ f -> f

defaultRenamer :: Renamer
defaultRenamer xs 0 = Renaming [] xs
defaultRenamer xs n = Renaming [] $ xs ++ sep ++ show (n+1)
  where
    sep
      | not (null xs) && isDigit (last xs) = "_"
      | otherwise = ""

withRenamer :: Name -> Renamer -> Name
Fixed x l `withRenamer` _ = Fixed x l
Unique n xs l _ `withRenamer` f = Unique n xs l f
Variant x xs _ `withRenamer` f = Variant x xs f

instance Eq Name where
  x == y = compareName x == compareName y

instance Ord Name where
  compare = comparing compareName

-- It's important that FixedNames come first so that they get added
-- first to the used names list in Jukebox.TPTP.Print.prettyRename.
compareName :: Name -> Either FixedName (Either Int64 (Name, [Name]))
compareName (Fixed xs _) = Left xs
compareName (Unique n _ _ _) = Right (Left n)
compareName (Variant x xs _) = Right (Right (x, xs))

instance Show Name where
  show (Fixed x ml) =
    show x ++
    case ml of
      Nothing -> ""
      Just l -> "[" ++ l ++ "]"
  show (Unique n xs ml f) =
    ys ++ "@" ++ show n ++
    case ml of
      Nothing -> ""
      Just l -> "[" ++ l ++ "]"
    where
      Renaming _ ys = f xs 0
  show (Variant x xs _) =
    "variant(" ++ show x ++
      concat [", " ++ show x | x <- xs] ++ ")"

class Named a where
  name :: a -> Name

instance Named [Char] where
  name x = Fixed (Basic (intern x)) Nothing

instance Named Integer where
  name n = name ("n" ++ show n)

instance Named Int where
  name = name . toInteger

instance Named Name where
  name = id

-- Get all names, including those only used as part of a variant.
allNames :: Named a => a -> [Name]
allNames x = gather [name x] []
  where
    gather [] xs = xs
    gather (x:xs) ys =
      sub x (x:gather xs ys)
    sub (Variant x xs _) ys =
      gather (x:xs) ys
    sub _ ys = ys

variant :: (Named a, Named b) => a -> [b] -> Name
variant x xs =
  Variant (name x) (map name xs) defaultRenamer

unvariant :: Name -> Maybe (Name, [Name])
unvariant (Variant x xs _) = Just (x, xs)
unvariant _ = Nothing

data a ::: b = a ::: b deriving Show

lhs :: (a ::: b) -> a
lhs (x ::: _) = x

rhs :: (a ::: b) -> b
rhs (_ ::: y) = y

instance Named a => Eq (a ::: b) where s == t = name s == name t
instance Named a => Ord (a ::: b) where compare = comparing name

instance Named a => Named (a ::: b) where
  name (a ::: _) = name a

newtype NameM a =
  NameM { unNameM :: State Int64 a }
    deriving (Functor, Applicative, Monad)

runNameM :: [Name] -> NameM a -> a
runNameM xs m =
  evalState (unNameM m) (maximum (0:[ succ n | Unique n _ _ _ <- xs ]))

newName :: Named a => a -> NameM Name
newName x = NameM $ do
  idx <- get
  let idx' = idx+1
  when (idx' < 0) $ error "Name.newName: too many names"
  put $! idx'
  return $! Unique idx' (base x) (label x) (renamer x)
