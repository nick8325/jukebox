-- Abstract syntax of TPTP problem clauses.
-- Try to preserve as much information as possible for standalone Monotonox.

{-# LANGUAGE BangPatterns #-}
module ReadProblem.Syntax where

import qualified Data.ByteString as BS
import Text.Parsec(SourcePos)

data Pos a = Pos { pos :: !SourcePos, it :: !a }
instance Show (Pos a) where
  show x = show (pos x)

data Formula = BinOp !(Pos Formula) !(Pos Formula) 
             | Not !(Pos Formula)
             | Quant !Quantifier ![Pos Binding] !(Pos Formula)
             | Equal !(Pos Term) !(Pos Term)
             | NotEqual !(Pos Term) !(Pos Term)
             | Lit !(Pos Term) deriving Show

data Term = Var !BS.ByteString | App !BS.ByteString ![Pos Term] deriving Show

data Connective = Or | And | Iff | Implies | Follows | Xor | Nor | Nand deriving Show
data Quantifier = ForAll | Exists deriving Show
data Type = Type | Bool | I | Named !BS.ByteString | Prod ![Type] | !Type :-> !Type deriving Show
data Binding = !BS.ByteString ::: !Type deriving Show

data Language = CNF | FOF | TFF deriving Show
data Kind = Axiom | Hypothesis | Definition | Assumption
          | Lemma | Theorem | Conjecture | NegatedConjecture | Question deriving Show

data TypeDeclaration = HasType !BS.ByteString !Type deriving Show
data IncludeDeclaration = Include !BS.ByteString !(Maybe [Tag]) deriving Show

-- A single TPTP input
data Input = IType !Tag !(Pos TypeDeclaration)
           | IInclude !(Pos IncludeDeclaration)
           | IFormula !Tag !Language !Kind !(Pos Formula)
             deriving Show
data Tag = String !BS.ByteString | Integer !Integer deriving Show

-- To make it easier when writing the parser, a type that represents
-- either a formula or a term
data Expression = Formula (Pos Formula) | Term (Pos Term) deriving Show
