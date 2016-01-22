-- -*- mode: haskell -*-

-- Roughly taken from the TPTP syntax reference
{
{-# OPTIONS_GHC -O2 -fno-warn-deprecated-flags #-}
{-# LANGUAGE BangPatterns #-}
module Jukebox.TPTP.Lexer(
  scan,
  Pos(..),
  Token(..),
  Punct(..),
  Defined(..),
  Keyword(..),
  TokenStream(..),
  Contents(..)) where

import Data.Word
import Data.Char
}

$alpha = [a-zA-Z0-9_]
$anything = [. \n]
@quoted = ($printable # [\\']) | \\ $printable
@dquoted = ($printable # [\\\"]) | \\ $printable

tokens :-
-- Comments and whitespace
"%" .* ;
"/*" (($anything # \*)* "*"+
      ($anything # [\/\*]))*
     ($anything # \*)* "*"* "*/" ; -- blech!
$white+ ;

-- Keywords.
"thf" { k Thf }
"tff" { k Tff }
"fof" { k Fof }
"cnf" { k Cnf }
"axiom" { k Axiom }
"hypothesis" { k Hypothesis }
"definition" { k Definition }
"assumption" { k Assumption }
"lemma" { k Lemma }
"theorem" { k Theorem }
"conjecture" { k Conjecture }
"negated_conjecture" { k NegatedConjecture }
"question" { k Question }
"plain" { k Plain }
"fi_domain" { k FiDomain }
"fi_hypothesis" { k FiHypothesis }
"fi_predicates" { k FiPredicates }
"type" { k Type }
"unknown" { k Unknown }
"include" { k Include }
-- Defined symbols.
"$true" { d DTrue }
"$false" { d DFalse }
"$equal" { d DEqual }
"$distinct" { d DDistinct }
"$itef" { d DItef }
"$itett" | "$itetf" { d DItet }
"$o" | "$oType" { d DO }
"$i" | "$iType" { d DI }
"$tType" { d DTType }
-- Atoms.
"$"{0,2} [a-z] $alpha* { Atom Normal . copy }
-- Atoms with funny quoted names (here we diverge from the official
-- syntax, which only allows the escape sequences \\ and \' in quoted
-- atoms: we allow \ to be followed by any printable character)
"'"  @quoted+ "'" { Atom Normal . unquote }
-- Vars are easy :)
[A-Z][$alpha]* { Var . copy }
-- Distinct objects, which are double-quoted
\" @dquoted+  \" { DistinctObject . unquote }
-- Integers
[\+\-]? (0 | [1-9][0-9]*)/($anything # $alpha) { Number . read }

-- Operators (FOF)
"("  { p LParen }  ")"   { p RParen }  "["  { p LBrack }   "]"  { p RBrack }
","  { p Comma }   "."   { p Dot }     "|"  { p Or }       "&"  { p And }
"~"  { p Not }     "<=>" { p Iff }     "=>" { p Implies }  "<=" { p Follows }
"<~>"{ p Xor }     "~|"  { p Nor }     "~&" { p Nand }     "="  { p Eq }
"!=" { p Neq }     "!"   { p ForAll }  "?"  { p Exists }   ":=" { p Let }
":-" { p LetTerm }
-- Operators (TFF)
":" { p Colon }    "*"   { p Times }   "+"  { p Plus }     ">"  { p FunArrow }
-- Operators (THF)
"^"  { p Lambda } "@" { p Apply }  "!!" { p ForAllLam }  "??"  { p ExistsLam }
"@+" { p Some }   "@-" { p The }   "<<" { p Subtype }    "-->" { p SequentArrow }
"!>" { p DependentProduct }        "?*" { p DependentSum }

{
data Pos = Pos {-# UNPACK #-} !Word {-# UNPACK #-} !Word deriving Show
data Token = Atom { keyword :: !Keyword, name :: String }
           | Defined { defined :: !Defined  }
           | Var { name :: String }
           | DistinctObject { name :: String }
           | Number { value :: !Integer }
           | Punct { kind :: !Punct }
           | Eof
           | Error

data Keyword = Normal
             | Thf | Tff | Fof | Cnf
             | Axiom | Hypothesis | Definition | Assumption
             | Lemma | Theorem | Conjecture | NegatedConjecture | Question
             | Plain | FiDomain | FiHypothesis | FiPredicates | Type | Unknown
             | Include deriving (Eq, Ord)

instance Show Keyword where
  show x =
    case x of {
      Normal -> "normal";
      Thf -> "thf"; Tff -> "tff"; Fof -> "fof"; Cnf -> "cnf";
      Axiom -> "axiom"; Hypothesis -> "hypothesis"; Definition -> "definition";
      Assumption -> "assumption"; Lemma -> "lemma"; Theorem -> "theorem";
      Conjecture -> "conjecture"; NegatedConjecture -> "negated_conjecture";
      Question -> "question"; Plain -> "plain"; FiDomain -> "fi_domain";
      FiHypothesis -> "fi_hypothesis"; FiPredicates -> "fi_predicates";
      Type -> "type"; Unknown -> "unknown"; Include -> "include" }

-- We only include defined names that need special treatment from the
-- parser here: you can freely make up any other names starting with a
-- '$' and they get turned into Atoms.
data Defined = DTrue | DFalse | DEqual | DDistinct | DItef | DItet
             | DO | DI | DTType deriving (Eq, Ord)

instance Show Defined where
  show x =
    case x of {
      DTrue -> "$true"; DFalse -> "$false"; DEqual -> "$equal";
      DDistinct -> "$distinct"; DItef -> "$itef"; DItet -> "$itet";
      DO -> "$o"; DI -> "$i"; DTType -> "$tType" }

data Punct = LParen | RParen | LBrack | RBrack | Comma | Dot
           | Or | And | Not | Iff | Implies | Follows | Xor | Nor | Nand
           | Eq | Neq | ForAll | Exists | Let | LetTerm -- FOF
           | Colon | Times | Plus | FunArrow -- TFF
           | Lambda | Apply | ForAllLam | ExistsLam
           | DependentProduct | DependentSum | Some | The
           | Subtype | SequentArrow -- THF
             deriving (Eq, Ord)

instance Show Punct where
  show x =
    case x of {
      LParen -> "("; RParen -> ")"; LBrack -> "["; RBrack -> "]";
      Comma -> ","; Dot -> "."; Or -> "|"; And -> "&"; Not -> "~";
      Iff -> "<=>"; Implies -> "=>"; Follows -> "<="; Xor -> "<~>";
      Nor -> "~|"; Nand -> "~&"; Eq -> "="; Neq -> "!="; ForAll -> "!";
      Exists -> "?"; Let -> ":="; Colon -> ":"; Times -> "*"; Plus -> "+";
      FunArrow -> ">"; Lambda -> "^"; Apply -> "@"; ForAllLam -> "!!";
      ExistsLam -> "??"; Some -> "@+"; The -> "@-"; Subtype -> "<<";
      SequentArrow -> "-->"; DependentProduct -> "!>"; DependentSum -> "?*" }

p x = const (Punct x)
k x = Atom x . copy
d x = const (Defined x)

copy :: String -> String
copy = id -- could change to a string interning function later

unquote :: String -> String
unquote x
  | null z = init y
  | otherwise = y ++ [z !! 1] ++ unquote (drop 2 z)
  where (y, z) = break (== '\\') x
    
-- The main scanner function, heavily modified from Alex's posn-bytestring wrapper.

data TokenStream = At {-# UNPACK #-} !Pos !Contents
data Contents = Cons !Token TokenStream

scan xs = go (Input (Pos 1 1) '\n' xs)
  where go inp@(Input pos _ xs) =
          case alexScan inp 0 of
                AlexEOF -> let t = At pos (Cons Eof t) in t
                AlexError _ -> let t = At pos (Cons Error t) in t
                AlexSkip  inp' len -> go inp'
                AlexToken inp' len act ->
                  At pos (act (take len xs) `Cons` go inp')

data AlexInput = Input {-# UNPACK #-} !Pos {-# UNPACK #-} !Char String

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar (Input p c xs) = c

{-# INLINE alexGetByte #-}
alexGetByte :: AlexInput -> Maybe (Word8,AlexInput)
alexGetByte i = fmap f (alexGetChar i)
  where f (c, i') = (fromIntegral (ord c), i')
{-# INLINE alexGetChar #-}
alexGetChar :: AlexInput -> Maybe (Char,AlexInput)
alexGetChar (Input p _ (x:xs)) =
  Just (x, Input (advance p x) x xs)
alexGetChar _ = Nothing

{-# INLINE advance #-}
advance :: Pos -> Char -> Pos
advance (Pos l c) '\t' = Pos  l    (c+8 - (c-1) `mod` 8)
advance (Pos l c) '\n' = Pos (l+1) 1
advance (Pos l c) _    = Pos  l    (c+1)
}
