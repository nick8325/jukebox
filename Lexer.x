-- -*- mode: haskell -*-
{
module Lexer where

import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL
import Data.Word
}

$digit = 0-9
$alpha = [a-zA-Z]

tokens :-
\%[^\n]* ;
$white+ ;
[a-z][$alpha]* { constr Atom }
[A-Z][$alpha]* { constr Var }
! { punct Bang }

{
constr :: (Pos -> BS.ByteString -> Token) -> Pos -> BSL.ByteString -> Token
constr con pos x = con pos (strict x)
  where strict = BS.concat . BSL.toChunks

punct :: Punct -> Pos -> BSL.ByteString -> Token
punct p pos x = Punct pos p

data Pos = Pos !Int !Int deriving Show
data Token = Atom { pos :: Pos, name :: BS.ByteString }
           | Var { pos :: Pos, name :: BS.ByteString }
           | Punct { pos :: Pos, kind :: Punct }
           | Error { pos :: Pos }
             deriving Show
data Punct = Bang deriving Show

--
-- Boring copy-and-pasted code for the main scanner function below.
--

-- Shamelessly lifted from Alex's posn-bytestring wrapper---the only
-- difference is it returns an Error token instead of calling error
-- when there's a lexical error, and it uses a simpler type for positions.
alexScanTokens str = go (Pos 1 1,'\n',str)
  where go inp@(pos,_,str) =
          case alexScan inp 0 of
                AlexEOF -> []
                AlexError _ -> [Error pos]
                AlexSkip  inp' len     -> go inp'
                AlexToken inp' len act -> act pos (BSL.take (fromIntegral len) str) : go inp'
type AlexInput = (Pos,     -- current position,
                  Char,         -- previous char
                  BSL.ByteString)        -- current input string

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar (p,c,s) = c

alexGetChar :: AlexInput -> Maybe (Char,AlexInput)
alexGetChar (p,_,cs) | BSL.null cs = Nothing
                     | otherwise = let c   = BSL.head cs
                                       cs' = BSL.tail cs
                                       p'  = alexMove p c
                                    in p' `seq` cs' `seq` Just (c, (p', c, cs'))
alexMove :: Pos -> Char -> Pos
alexMove (Pos l c) '\t' = Pos  l     (((c+7) `div` 8)*8+1)
alexMove (Pos l c) '\n' = Pos (l+1)   1
alexMove (Pos l c) _    = Pos  l     (c+1)
}
