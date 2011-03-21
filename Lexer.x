-- -*- mode: haskell -*-

-- Roughly taken from the TPTP syntax reference
{
{-# LANGUAGE BangPatterns #-}
module Lexer(alexScanTokens, Pos(..), Token(..)) where

import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL
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
"$"{0,2}[a-z][$alpha]* { constr Atom }
-- Atoms with funny quoted names (here we diverge from the official
-- syntax, which only allows the escape sequences \\ and \' in quoted
-- atoms: we allow \ to be followed by any printable character)
"'" (($printable # [\\']) | \\ $printable)+  "'" { constrUnquote Atom }
-- Vars are easy :)
[A-Z][$alpha]* { constr Var }
-- Distinct objects, which are double-quoted
\" (($printable # [\\\"]) | \\ $printable)+  \" { constrUnquote DistinctObject }
-- Integers
[\+\-]? (0 | [1-9][0-9]*)/($anything # $alpha) { \p s -> Number p (readNumber s) }

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
{ constr Punct }

{
constr :: (Pos -> BS.ByteString -> Token) -> Pos -> BSL.ByteString -> Token
constr con pos x = con pos (strict x)
  where strict x = case BSL.toChunks x of
                     [] -> BS.empty
                     [x] -> BS.copy x
                     xs -> BS.concat xs

constrUnquote :: (Pos -> BS.ByteString -> Token) -> Pos -> BSL.ByteString -> Token
constrUnquote con pos x = constr con pos (unquote (BSL.tail x))

unquote :: BSL.ByteString -> BSL.ByteString
unquote x | BSL.null z = BSL.init y
          | otherwise = y `BSL.append` (BSL.index z 1 `BSL.cons'` unquote (BSL.drop 2 z))
          where (y, z) = BSL.break (== '\\') x
    
readNumber :: BSL.ByteString -> Integer
readNumber x | BSL.null r = n
  where Just (n, r) = BSL.readInteger x

data Pos = Pos !Int !Int deriving Show
data Token = Atom { pos :: !Pos, name :: !BS.ByteString }
           | Var { pos :: !Pos, name :: !BS.ByteString }
           | DistinctObject { pos :: !Pos, name :: !BS.ByteString }
           | Number { pos :: !Pos, value :: Integer }
           | Punct { pos :: !Pos, kind :: !BS.ByteString }
           | Error { pos :: !Pos }
             deriving Show

--
-- Boring copy-and-pasted code for the main scanner function below.
--

-- Shamelessly lifted from Alex's posn-bytestring wrapper---the only
-- difference is it returns an Error token instead of calling error
-- when there's a lexical error, and it uses a simpler type for positions.
alexScanTokens str = go (Input (Pos 1 1) '\n' str)
  where go inp@(Input pos _ str) =
          case alexScan inp 0 of
                AlexEOF -> []
                AlexError _ -> [Error pos]
                AlexSkip  inp' len     -> go inp'
                AlexToken inp' len act -> act pos (BSL.take (fromIntegral len) str) : go inp'
data AlexInput = Input {-# UNPACK #-} !Pos {-# UNPACK #-} !Char {-# UNPACK #-} !BSL.ByteString

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar (Input p c s) = c

{-# INLINE alexGetChar #-}
alexGetChar :: AlexInput -> Maybe (Char,AlexInput)
alexGetChar (Input p _ cs) | BSL.null cs = Nothing
                           | otherwise = let c   = BSL.head cs
                                             !next = Input (alexMove p c) c (BSL.tail cs)
                                         in Just (c, next)

{-# INLINE alexMove #-}
alexMove :: Pos -> Char -> Pos
alexMove (Pos l c) '\t' = Pos  l     (((c+7) `div` 8)*8+1)
alexMove (Pos l c) '\n' = Pos (l+1)   1
alexMove (Pos l c) _    = Pos  l     (c+1)
}
