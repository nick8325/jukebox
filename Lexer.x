-- -*- mode: haskell -*-

-- Roughly taken from the TPTP syntax reference
{
{-# OPTIONS_GHC -O2 -fno-warn-deprecated-flags #-}
{-# LANGUAGE BangPatterns #-}
module Lexer(scan, Pos(..), Token(..), Punct(..), Defined(..), Keyword(..), TokenStream(..), Contents(..), alexGetChar) where

import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL
import Data.ByteString.Lazy.Internal
import Data.Word
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
[\+\-]? (0 | [1-9][0-9]*)/($anything # $alpha) { Number . readNumber }

-- Operators (FOF)
"("  { p LParen }  ")"   { p RParen }  "["  { p LBrack }   "]"  { p RBrack }
","  { p Comma }   "."   { p Dot }     "|"  { p Or }       "&"  { p And }
"~"  { p Not }     "<=>" { p Iff }     "=>" { p Implies }  "<=" { p Follows }
"<~>"{ p Xnor }    "~|"  { p Nor }     "~&" { p Nand }     "="  { p Eq }
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
data Token = Atom { keyword :: !Keyword, name :: !BS.ByteString }
           | Defined { defined :: !Defined, name :: !BS.ByteString }
           | Var { name :: !BS.ByteString }
           | DistinctObject { name :: !BS.ByteString }
           | Number { value :: !Integer }
           | Punct { kind :: !Punct }
             deriving (Eq, Show)

data Keyword = Normal
             | Thf | Tff | Fof | Cnf
             | Axiom | Hypothesis | Definition | Assumption
             | Lemma | Theorem | Conjecture | NegatedConjecture | Question
             | Plain | FiDomain | FiHypothesis | FiPredicates | Type | Unknown
             | Include deriving (Eq, Ord, Show)

-- We only include defined names that need special treatment from the
-- parser here: you can freely make up any other names starting with a
-- '$' and they get turned into Atoms.
data Defined = DTrue | DFalse | DEqual | DDistinct | DItef | DItet
             | DO | DI | DTType deriving (Eq, Ord, Show)

data Punct = LParen | RParen | LBrack | RBrack | Comma | Dot
           | Or | And | Not | Iff | Implies | Follows | Xnor | Nor | Nand
           | Eq | Neq | ForAll | Exists | Let | LetTerm -- FOF
           | Colon | Times | Plus | FunArrow -- TFF
           | Lambda | Apply | ForAllLam | ExistsLam
           | DependentProduct | DependentSum | Some | The
           | Subtype | SequentArrow -- THF
             deriving (Eq, Ord, Show)

p x = const (Punct x)
k x = Atom x . copy
d x = Defined x . copy

copy :: BS.ByteString -> BS.ByteString
copy = id -- could change to a string interning function later

unquote :: BS.ByteString -> BS.ByteString
unquote x =
  case BSL.toChunks (BSL.tail (unquote' x)) of
    [] -> BS.empty
    [x] -> copy x
    xs -> BS.concat xs

unquote' :: BS.ByteString -> BSL.ByteString
unquote' x | BS.null z = chunk (BS.init y) Empty
           | otherwise = chunk y (BS.index z 1 `BSL.cons'` unquote' (BS.drop 2 z))
           where (y, z) = BS.break (== '\\') x
    
readNumber :: BS.ByteString -> Integer
readNumber x | BS.null r = n
  where Just (n, r) = BS.readInteger x

-- The main scanner function, heavily modified from Alex's posn-bytestring wrapper.

data TokenStream = At {-# UNPACK #-} !Pos !Contents
data Contents = Nil | Cons !Token TokenStream | Error

scan xs = go (Input (Pos 1 1) '\n' BS.empty xs)
  where go inp@(Input pos _ x xs) =
          case alexScan inp 0 of
                AlexEOF -> At pos Nil
                AlexError _ -> At pos Error
                AlexSkip  inp' len -> go inp'
                AlexToken inp' len act ->
                  let token | len <= BS.length x = BS.take len x
                            | otherwise = BS.concat (BSL.toChunks (BSL.take (fromIntegral len) (chunk x xs)))
                  in At pos (act token `Cons` go inp')

data AlexInput = Input {-# UNPACK #-} !Pos {-# UNPACK #-} !Char {-# UNPACK #-} !BS.ByteString BSL.ByteString

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar (Input p c x xs) = c

{-# INLINE alexGetChar #-}
alexGetChar :: AlexInput -> Maybe (Char,AlexInput)
alexGetChar (Input p _ x xs) | not (BS.null x) = getCharNonEmpty p x xs
alexGetChar (Input p _ _ (Chunk x xs)) = getCharNonEmpty p x xs
alexGetChar (Input p _ _ Empty) = Nothing
{-# INLINE getCharNonEmpty #-}
getCharNonEmpty p x xs =
  let !c = BS.head x
      !next = Input (advance p c) c (BS.tail x) xs
  in Just (c, next)

{-# INLINE advance #-}
advance :: Pos -> Char -> Pos
advance (Pos l c) '\t' = Pos  l    (c+8 - (c-1) `mod` 8)
advance (Pos l c) '\n' = Pos (l+1) 1
advance (Pos l c) _    = Pos  l    (c+1)
}
