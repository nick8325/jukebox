-- Parse little bits of TPTP, e.g. a prelude for a particular tool.

module Jukebox.TPTP.ParseSnippet where

import Jukebox.TPTP.ClauseParser as TPTP.ClauseParser
import Jukebox.TPTP.Parsec as TPTP.Parsec
import Jukebox.TPTP.Lexer
import Jukebox.Name
import Jukebox.Form
import Control.Applicative
import qualified Data.Map.Strict as Map
import Data.List
import Control.Monad.State.Strict

tff, cnf :: [(String, Type)] -> [(String, Function)] -> String -> Form
tff = form TPTP.ClauseParser.tff
cnf = form TPTP.ClauseParser.cnf

form :: Parser a -> [(String, Type)] -> [(String, Function)] -> String -> a
form parser types funs str =
  case run_ (parser <* eof)
            (UserState (MkState [] (Map.fromList funs)) (scan str)) of
    Ok (UserState (MkState _ funs') (At _ (Cons Eof _))) res
      | Map.fromList funs /= funs' ->
        error $ "ParseSnippet: function implicitly defined: " ++
                show (map snd (Map.toList funs' \\ funs))
      | otherwise -> res
    Ok{} -> error "ParseSnippet: lexical error"
    TPTP.Parsec.Error _ msg -> error $ "ParseSnippet: parse error: " ++ msg
    Expected _ exp -> error $ "ParseSnippet: parse error: expected " ++ show exp
