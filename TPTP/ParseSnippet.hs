-- Parse little bits of TPTP, e.g. a prelude for a particular tool.

module TPTP.ParseSnippet where

import TPTP.ClauseParser
import TPTP.Parsec
import TPTP.Lexer
import Name
import Form
import qualified Data.ByteString.Lazy.Char8 as BSL
import qualified Data.ByteString.Char8 as BS
import Control.Applicative
import qualified Map

tff, cnf :: [(String, Type)] -> [(String, Function)] -> String -> NameM Form
tff = form TPTP.ClauseParser.tff
cnf = form TPTP.ClauseParser.cnf

form parser types funs str = supply (form' parser types funs str)

form' parser types funs str cl =
  let state0 = MkState [] (pack types) (pack funs) Map.empty iType cl
      pack xs = Map.fromList [(BS.pack x, y) | (x, y) <- xs]
      iType =
        case lookup "$i" types of
          Just x -> x
          Nothing -> error "ParseSnippet: use explicit type declarations" in
  case run_ (parser <* eof)
            (UserState state0 (scan (BSL.pack str))) of
    Ok (UserState state (At _ (Cons Eof _))) res ->
      case state of
        MkState _ types' funs' vars _ _
          | pack types /= types' ->
            error $ "ParseSnippet: type implicitly defined: " ++ show types'
          | pack funs /= funs' ->
            error $ "ParseSnippet: function implicitly defined: " ++ show funs'
        MkState _ _ _ _ _ cl' ->
          fmap (const res) cl'
    Ok{} -> error "ParseSnippet: lexical error"
    TPTP.Parsec.Error _ msg -> error $ "ParseSnippet: parse error: " ++ msg
    Expected _ exp -> error $ "ParseSnippet: parse error: expected " ++ show exp
