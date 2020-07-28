-- -*- mode: haskell -*-

-- Roughly taken from the TPTP syntax reference
{
{-# OPTIONS_GHC -O2 -fno-warn-deprecated-flags #-}
{-# LANGUAGE BangPatterns, OverloadedStrings #-}
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
import Data.Ratio
import Codec.Binary.UTF8.String
import Data.Symbol
}

$alpha = [a-zA-Z0-9_]
$anything = [. \n]
@quoted = ($printable # [\\']) | \\ $printable
@dquoted = ($printable # [\\\"]) | \\ $printable
@pnum = [1-9][0-9]*
@num  = 0 | @pnum

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
"tcf" { k Tcf }
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
"'"  @quoted+ "'" { Atom Normal . copy . unquote }
-- Vars are easy :)
[A-Z][$alpha]* { Var . copy }
-- Distinct objects, which are double-quoted
\" @dquoted+  \" { DistinctObject . copy . unquote }
-- Numbers
[\+\-]? @num/($anything # $alpha) { Number . read }
[\+\-]? @num\/@pnum { Rational . readRational }
[\+\-]? @num\.@num { Real . readReal }
[\+\-]? @num(\.@num)?[eE]@num { Real . readReal }

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
data Token = Atom { keyword :: !Keyword, tokenName :: {-# UNPACK #-} !Symbol }
           | Defined { defined :: !Defined  }
           | Var { tokenName :: {-# UNPACK #-} !Symbol }
           | DistinctObject { tokenName :: {-# UNPACK #-} !Symbol }
           | Number { value :: !Integer }
           | Rational { ratValue :: !Rational }
           | Real { ratValue :: !Rational }
           | Punct { kind :: !Punct }
           | Eof
           | Error

data Keyword = Normal
             | Thf | Tff | Fof | Tcf | Cnf
             | Axiom | Hypothesis | Definition | Assumption
             | Lemma | Theorem | Conjecture | NegatedConjecture | Question
             | Plain | FiDomain | FiHypothesis | FiPredicates | Type | Unknown
             | Include deriving (Eq, Ord)

instance Show Keyword where
  show x =
    case x of {
      Normal -> "normal";
      Thf -> "thf"; Tff -> "tff"; Fof -> "fof"; Tcf -> "tcf"; Cnf -> "cnf";
      Axiom -> "axiom"; Hypothesis -> "hypothesis"; Definition -> "definition";
      Assumption -> "assumption"; Lemma -> "lemma"; Theorem -> "theorem";
      Conjecture -> "conjecture"; NegatedConjecture -> "negated_conjecture";
      Question -> "question"; Plain -> "plain"; FiDomain -> "fi_domain";
      FiHypothesis -> "fi_hypothesis"; FiPredicates -> "fi_predicates";
      Type -> "type"; Unknown -> "unknown"; Include -> "include" }

-- We only include defined names that need special treatment from the
-- parser here: you can freely make up any other names starting with a
-- '$' and they get turned into Atoms.
data Defined =
    DTrue | DFalse | DDistinct | DItef | DItet
  | DO | DI | DTType
  deriving (Eq, Ord)

instance Show Defined where
  show x =
    case x of {
      DTrue -> "$true"; DFalse -> "$false";
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

showPunct :: Punct -> Symbol
showPunct x =
  case x of {
    LParen -> "("; RParen -> ")"; LBrack -> "["; RBrack -> "]";
    Comma -> ","; Dot -> "."; Or -> "|"; And -> "&"; Not -> "~";
    Iff -> "<=>"; Implies -> "=>"; Follows -> "<="; Xor -> "<~>";
    Nor -> "~|"; Nand -> "~&"; Eq -> "="; Neq -> "!="; ForAll -> "!";
    Exists -> "?"; Let -> ":="; Colon -> ":"; Times -> "*"; Plus -> "+";
    FunArrow -> ">"; Lambda -> "^"; Apply -> "@"; ForAllLam -> "!!";
    ExistsLam -> "??"; Some -> "@+"; The -> "@-"; Subtype -> "<<";
    SequentArrow -> "-->"; DependentProduct -> "!>"; DependentSum -> "?*";
    LetTerm -> ":-" }

instance Show Punct where
  show = unintern . showPunct

p x = const (Punct x)
k x = Atom x . copy
d x = const (Defined x)

copy :: String -> Symbol
copy = intern

unquote :: String -> String
unquote (_:x)
  | null z = init y
  | otherwise = y ++ [z !! 1] ++ unquote (drop 1 z)
  where (y, z) = break (== '\\') x

readRational :: String -> Rational
readRational = readSigned (readNum (\m ('/':xs) -> readNum (\n [] -> m % n) xs))

readReal :: String -> Rational
readReal = readSigned $ readNum $ \m xs ->
  case xs of
    '.':ys -> readDigits (readExp m) ys
    _ -> readExp m [] xs
  where
    readExp n ds ('e':xs) =
      readSign (\f -> readNum (result n ds . f)) xs
    readExp n ds ('E':xs) =
      readSign (\f -> readNum (result n ds . f)) xs
    readExp n ds xs = result n ds 0 xs
    result n ds e [] =
      (fromInteger n +
       fromInteger (read ds) / (10^length ds)) * (10^^e)

readSigned :: (String -> Rational) -> String -> Rational
readSigned f xs = readSign (\g -> g . f) xs

readSign :: Num a => ((a -> a) -> String -> Rational) -> String -> Rational
readSign f ('+':xs) = f id xs
readSign f ('-':xs) = f negate xs
readSign f xs = f id xs

readNum :: (Integer -> String -> Rational) -> String -> Rational
readNum f xs = readDigits (f . read) xs

readDigits :: (String -> String -> Rational) -> String -> Rational
readDigits f xs = f ys zs
  where
    (ys, zs) = span isDigit xs

-- The main scanner function, heavily modified from Alex's posn-bytestring wrapper.

data TokenStream = At {-# UNPACK #-} !Pos !Contents
data Contents = Cons !Token TokenStream

scan xs = go (Input (Pos 1 1) '\n' [] xs)
  where go inp@(Input pos _ _ xs) =
          case alexScan inp 0 of
                AlexEOF -> let t = At pos (Cons Eof t) in t
                AlexError _ -> let t = At pos (Cons Error t) in t
                AlexSkip  inp' _ -> go inp'
                AlexToken inp' len act ->
                  At pos (act (take len xs) `Cons` go inp')

data AlexInput = Input {-# UNPACK #-} !Pos {-# UNPACK #-} !Char [Word8] String

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar (Input _ c _ _) = c

{-# INLINE alexGetByte #-}
alexGetByte :: AlexInput -> Maybe (Word8,AlexInput)
alexGetByte (Input pos prev (b:bs) xs) =
  Just (b, Input pos prev bs xs)
alexGetByte (Input pos _ [] (x:xs)) =
  case encodeChar x of
    b:bs -> Just (b, Input (advance pos x) x bs xs)
alexGetByte (Input _ _ [] []) = Nothing

{-# INLINE advance #-}
advance :: Pos -> Char -> Pos
advance (Pos l c) '\t' = Pos  l    (c+8 - (c-1) `mod` 8)
advance (Pos l _) '\n' = Pos (l+1) 1
advance (Pos l c) _    = Pos  l    (c+1)
}
