module Parser where

import Text.Parsec
import Lexer
import Formula
import Progress
import TPTP

data ParseState = ParseState
  { problem :: !(Problem Formula),
    tokens :: !Int }

type Parser = ParsecT TokenStream ParseState (ProgressT TPTP)
