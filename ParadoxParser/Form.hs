module ParadoxParser.Form where

{-
Paradox/Equinox -- Copyright (c) 2003-2007, Koen Claessen, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
-}

import Data.Set as S( Set )
import qualified Data.Set as S
import Data.Map as M( Map )
import qualified Data.Map as M
import Data.List 

import ParadoxParser.Name

----------------------------------------------------------------------
-- Type

data Type
  = Type
  { tname  :: Name
  , tsize  :: Maybe Int
  , tequal :: Equality
  }
 deriving ( Eq, Ord )

data Equality
  -- this order matters!
  = Safe
  | Half
  | Full
 deriving ( Eq, Ord, Show )

instance Show Type where
  show (Type t s e) = show t ++ showSize s ++ showEq e
   where
    showEq Half = "_eq"
    showEq Full = "_heq"
    showEq _    = ""
    
    showSize Nothing  = ""
    showSize (Just n) = "_" ++ show n

tdomain :: Type -> Maybe Int
tdomain t =
  case tsize t of
    Nothing -> Nothing
    Just n  -> case tequal t of
                 Safe -> Just n
                 Half -> Just (n+1)
                 Full -> Nothing

top, bool :: Type
top  = Type (prim "Top")  Nothing  Full
bool = Type (prim "Bool") (Just 2) Safe

data Typing
  = [Type] :-> Type
  | V Type
 deriving ( Eq, Ord )

opers :: Show a => String -> [a] -> ShowS
opers op xs = foldr (.) id (intersperse (showString op) (map shows xs))

commas :: Show a => [a] -> ShowS
commas = opers ","

instance Show Typing where
  showsPrec n (V t)       = showsPrec n t
  showsPrec n ([]  :-> t) = showsPrec n t
  showsPrec n ([s] :-> t) = showsPrec n s
                          . showString " -> "
                          . showsPrec n t
  showsPrec n (ts  :-> t) = showString "("
                          . commas ts
                          . showString ") -> "
                          . showsPrec n t

----------------------------------------------------------------------
-- Symbol

data Symbol
  = Name ::: Typing
 deriving ( Eq, Ord )

instance Show Symbol where
{-
  showsPrec n (x ::: V t) | t /= top =
      showsPrec n x
    . showString ":"
    . showsPrec n t
-}
  showsPrec n (x ::: _) =
      showsPrec n x

arity :: Symbol -> Int
arity (_ ::: (xs :-> _)) = length xs
arity _                  = 0

typing :: Symbol -> Typing
typing (_ ::: tp) = tp

isVarSymbol :: Symbol -> Bool
isVarSymbol (_ ::: V _) = True
isVarSymbol _           = False

isPredSymbol :: Symbol -> Bool
isPredSymbol s@(_ ::: (_ :-> t)) = t == bool && arity s > 0
isPredSymbol _                 = False

isFunSymbol s = not (isVarSymbol s || isPredSymbol s || s == (tr ::: ([] :-> bool)))
isConstantSymbol s = isFunSymbol s && arity s == 0


----------------------------------------------------------------------
-- Term

data Term
  = Fun Symbol [Term]
  | Var Symbol
 deriving ( Eq, Ord )

typ :: Term -> Type
typ (Var (_ ::: V tp))         = tp
typ (Fun (_ ::: (_ :-> tp)) _) = tp

instance Show Term where
  showsPrec n (Fun f []) = showsPrec n f
  showsPrec n (Fun f xs) = showsPrec n f
                         . showString "("
                         . commas xs
                         . showString ")"
  showsPrec n (Var x)    = showsPrec n x

var :: Type -> Int -> Symbol
var t i = (vr % i) ::: V t

data Atom
  = Term :=: Term
 deriving ( Eq, Ord )

instance Show Atom where
  showsPrec n (a :=: b)
    | b == truth = showsPrec n a
    | otherwise  = showsPrec n a
                 . showString " = "
                 . showsPrec n b

truth :: Term
truth = Fun (tr ::: ([] :-> bool)) []

prd :: Symbol -> [Term] -> Atom
prd p ts = Fun p ts :=: truth

data Bind a
  = Bind [Symbol] a
 deriving ( Eq, Ord )

instance Show a => Show (Bind a) where
  showsPrec n (Bind x a) = showString "["
                         . showsPrec n x
                         . showString "] : "
                         . showsPrec n a

data Form
  = Atom Atom
  | And [Form]
  | Or [Form]
  | Form `Equiv` Form
  | Not Form
  | ForAll (Bind Form)
  | Exists (Bind Form)
  | Xor Form Form
  | Imp Form Form
  | Foll Form Form
  | Nor Form Form
  | Nand Form Form
 deriving ( Eq, Ord, Show )

----------------------------------------------------------------------
-- input clauses

data Kind
  = Axiom
  | Conjecture
 deriving ( Eq, Ord, Show )

data Input a
  = Input
  { kind :: Kind
  , tag  :: String
  , what :: a
  }
 deriving ( Eq, Ord, Show )

type Problem = [Input Form]

----------------------------------------------------------------------
-- answers

data ConjectureAnswer
  = CounterSatisfiable
  | Theorem -- CounterUnsatisfiable :-)
  | FinitelyCounterUnsatisfiable
  | NoAnswerConjecture NoAnswerReason
 deriving ( Eq )

instance Show ConjectureAnswer where
  show CounterSatisfiable           = "CounterSatisfiable"
  show Theorem                      = "Theorem"
  show FinitelyCounterUnsatisfiable = "FinitelyCounterUnsatisfiable"
  show (NoAnswerConjecture r)       = show r

data ClauseAnswer
  = Satisfiable
  | Unsatisfiable
  | FinitelyUnsatisfiable
  | NoAnswerClause NoAnswerReason
 deriving ( Eq )

instance Show ClauseAnswer where
  show Satisfiable           = "Satisfiable"
  show Unsatisfiable         = "Unsatisfiable"
  show FinitelyUnsatisfiable = "FinitelyUnsatisfiable"
  show (NoAnswerClause r)    = show r

data NoAnswerReason
  = GaveUp
  | Timeout
 deriving ( Show, Eq )

toConjectureAnswer :: ClauseAnswer -> ConjectureAnswer
toConjectureAnswer Satisfiable           = CounterSatisfiable
toConjectureAnswer Unsatisfiable         = Theorem
toConjectureAnswer FinitelyUnsatisfiable = FinitelyCounterUnsatisfiable
toConjectureAnswer (NoAnswerClause r)    = NoAnswerConjecture r

----------------------------------------------------------------------
-- the end.
