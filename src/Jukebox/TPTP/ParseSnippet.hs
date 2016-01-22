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

tff, cnf :: [(String, Type)] -> [(String, Function)] -> String -> NameM Form
tff = form TPTP.ClauseParser.tff
cnf = form TPTP.ClauseParser.cnf

form parser types funs str = supply (form' parser types funs str)

form' parser types funs str cl =
  let state0 = MkState [] (Map.fromList types) (Map.fromList funs) Map.empty iType cl
      iType =
        case lookup "$i" types of
          Just x -> x
          Nothing -> error "ParseSnippet: use explicit type declarations" in
  case run_ (parser <* eof)
            (UserState state0 (scan str)) of
    Ok (UserState state (At _ (Cons Eof _))) res ->
      case state of
        MkState _ types' funs' vars _ _
          | Map.fromList types /= types' ->
            error $ "ParseSnippet: type implicitly defined: " ++
                    show (map snd (Map.toList types' \\ types))
          | Map.fromList funs /= funs' ->
            error $ "ParseSnippet: function implicitly defined: " ++
                    show (map snd (Map.toList funs' \\ funs))
        MkState _ _ _ _ _ cl' ->
          fmap (const res) cl'
    Ok{} -> error "ParseSnippet: lexical error"
    TPTP.Parsec.Error _ msg -> error $ "ParseSnippet: parse error: " ++ msg
    Expected _ exp -> error $ "ParseSnippet: parse error: expected " ++ show exp
