-- -*- mode: haskell -*-

-- Roughly taken from the TPTP syntax reference
{
{-# OPTIONS_GHC -O2 #-}
{-# LANGUAGE BangPatterns #-}
module Lexer(scan, Pos(..), Token(..)) where

import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL
import Data.ByteString.Lazy.Internal
import Data.Word
}

$alpha = [a-zA-Z0-9_]
$anything = [. \n]

tokens :-
-- Comments and whitespace
"%" .* ;
"/*" (($anything # \*)* "*"+
      ($anything # [\/\*]))*
     ($anything # \*)* "*"* "*/" ; -- blech!
$white+ ;

-- Atoms. Might be best to move the $- and $$-atoms into their own token type?
"$"{0,2}[a-z][$alpha]* { Atom . copy }
-- Atoms with funny quoted names (here we diverge from the official
-- syntax, which only allows the escape sequences \\ and \' in quoted
-- atoms: we allow \ to be followed by any printable character)
"'" (($printable # [\\']) | \\ $printable)+  "'" { Atom . unquote }
-- Vars are easy :)
[A-Z][$alpha]* { Var . copy }
-- Distinct objects, which are double-quoted
\" (($printable # [\\\"]) | \\ $printable)+  \" { DistinctObject . unquote }
-- Integers
[\+\-]? (0 | [1-9][0-9]*)/($anything # $alpha) { Number . readNumber }

-- Operators
"(" | ")" | "[" | "]" |
"," | "." |
"|" | "&" | "@" | ":" | 
":=" | ":-" |
"^" | "!>" | "?*" | "@+" | "@-" |
"!!" | "??" | "<<" |
"!" | "?" | "<=>" | "=>" | "<=" |
"<~>" | "~|" | "~&" | "~" | "-->" |
"=" | "!=" | "*" | "+" | ">" | "<"
{ Punct }

{
copy :: BS.ByteString -> BS.ByteString
copy = id -- could change to a string interning function later

unquote :: BS.ByteString -> BS.ByteString
unquote x =
  case BSL.toChunks (unquote' x) of
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

data Pos = Pos !Word !Word deriving Show
data Token = Atom { name :: !BS.ByteString, pos :: !Pos }
           | Var { name :: !BS.ByteString, pos :: !Pos }
           | DistinctObject { name :: !BS.ByteString, pos :: !Pos }
           | Number { value :: Integer, pos :: !Pos }
           | Punct { kind :: !BS.ByteString, pos :: !Pos }
           | Error { pos :: !Pos }
             deriving Show

-- The main scanner function, heavily modified from Alex's posn-bytestring wrapper.

scan xs = go (Input (Pos 1 1) '\n' BS.empty xs)
  where go inp@(Input pos _ x xs) =
          case alexScan inp 0 of
                AlexEOF -> []
                AlexError _ -> [Error pos]
                AlexSkip  inp' len     -> go inp'
                AlexToken inp' len act | len <= BS.length x -> act (BS.take len x) pos : go inp'
                                       | otherwise ->
                                         let token = BSL.take (fromIntegral len) (chunk x xs)
                                         in act (BS.concat (BSL.toChunks token)) pos : go inp'
data AlexInput = Input {-# UNPACK #-} !Pos {-# UNPACK #-} !Char {-# UNPACK #-} !BS.ByteString !BSL.ByteString

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar (Input p c x xs) = c

{-# INLINE alexGetChar #-}
alexGetChar :: AlexInput -> Maybe (Char,AlexInput)
alexGetChar (Input p _ x xs) | BS.null x = refill p xs
                             | otherwise = getCharNonEmpty p x xs
{-# NOINLINE refill #-} -- this is the slow path
refill p Empty = Nothing
refill p (Chunk x xs) = getCharNonEmpty p x xs
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
