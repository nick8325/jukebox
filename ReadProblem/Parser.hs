-- Parse single TPTP clauses into abstract syntax.

{-# LANGUAGE BangPatterns, MultiParamTypeClasses #-}
module ReadProblem.Parser where

import Text.Parsec hiding (satisfy, eof, token, runParser)
import Text.Parsec.Error
import Text.Parsec.Pos
import Text.Parsec.Prim hiding (runParser, token)
import Control.Monad.Identity
import qualified Data.ByteString.Lazy.Char8 as BSL
import qualified Data.ByteString.Char8 as BS

import ReadProblem.Lexer hiding (At, Error, Include, keyword, defined, kind)
import qualified ReadProblem.Lexer as L
import ReadProblem.Syntax

-- The parser monad

type Parser = Parsec Contents ()
type ParsecState = State Contents ()

instance Stream Contents Identity Token where
  -- dummy instance---we have our own combinators for fetching from
  -- the stream, since parsec struggles with our special Error token.
  uncons = error "uncons: not implemented"

-- The initial Parsec state.
openFile :: FilePath -> TokenStream -> ParsecState
openFile file (L.At (Pos l c) ts) = State ts pos ()
  where pos = newPos file (fromIntegral l) (fromIntegral c)

runParser :: Parser a -> ParsecState -> Either ParseError (a, ParsecState)
runParser p state =
  case runIdentity (consumed (runIdentity (runParsecT p state))) of
    Error e -> Left e
    Ok x s _ -> Right (x, s)
  where consumed (Consumed x) = x
        consumed (Empty x) = x

-- Wee function for testing.
testParser :: Parser a -> String -> Either ParseError a
testParser p s = fmap fst (runParser p (openFile "<test input>" (scan (BSL.pack s))))

eof :: ParsecState -> Bool
eof (State Nil _ _) = True
eof _ = False

-- Primitive parsers.

satisfy p = mkPT $ \s ->
  let err c msg = Identity (c (Identity (Error (newErrorMessage msg (statePos s))))) in
  case stateInput s of
    Nil -> err Empty (UnExpect "end of input")
    Cons t (L.At (Pos l c) !ts) ->
      if p t
         then let !pos' = flip setSourceLine (fromIntegral l) .
                          flip setSourceColumn (fromIntegral c) $ statePos s
                  !s' = s { statePos = pos', stateInput = ts }
              in Identity (Consumed (Identity (Ok t s' (unknownError s))))
         else err Empty (UnExpect (show t))
    L.Error -> err Consumed (Message "lexical error")

keyword' p = satisfy p'
  where p' Atom { L.keyword = k } = p k
        p' _ = False
keyword k = keyword' (== k) <?> show k
punct' p = satisfy p'
  where p' Punct { L.kind = k } = p k
        p' _ = False
punct k = punct' (== k) <?> show k
defined' p = fmap defined (satisfy p')
  where p' Defined { L.defined = d } = p d
        p' _ = False
defined k = defined' (== k) <?> show k
var = fmap name (satisfy p) <?> "variable"
  where p Var{} = True
        p _ = False
number = fmap number (satisfy p) <?> "number"
  where p Number{} = True
        p _ = False
atom = fmap name (keyword' (const True)) <?> "atom"

-- Combinators.

parens, bracks :: Parser a -> Parser a
parens p = between (punct LParen) (punct RParen) p
bracks p = between (punct LBrack) (punct RBrack) p

binExpr :: Parser a -> Parser (a -> a -> Parser a) -> Parser a
binExpr leaf op = do
  lhs <- parens (binExpr leaf op) <|> leaf
  do { f <- op; rhs <- binExpr leaf op; return (f lhs rhs) } <|> return lhs

-- Parsing formulae.

input :: Parser Input
input = declaration Cnf (formulaIn CNF) <|>
        declaration Fof (formulaIn FOF) <|>
        declaration Tff (\tag -> formulaIn TFF tag <|> typeDeclaration tag)
  where declaration k p = do
          k
          res <- parens $ do
            t <- tag
            punct Comma
            p t
          punct Dot
          return res
        formulaIn lang tag = do
          k <- kind
          form <- formula
          return (IFormula tag lang k form)

include :: Parser IncludeDeclaration
include = do
  keyword L.Include
  pos <- here
  res <- parens $ do
    name <- atom
    clauses <- do { punct Comma
                  ; fmap Just (bracks (sepBy1 tag (punct Comma))) } <|> return Nothing
    return (Include name clauses)
  punct Dot
  return res

atomic = parens term <|> ((function <|> special) <?> "term")
  where special = do
          x <- var <|> number
          return (Atomic x [])
        function = do
          x <- atom <|> defined' (const True)
          args <- parens (sepBy1 atomic (punct Comma)) <|> return []
          return (Atomic x args)

literal = atomic `binExpr` (punct Eq <|> punct Neq)
unitaryTerm = liftM2 Monop (punct Not) unitaryTerm <|>
              quantifiedTerm <|>
              literal

quantifiedTerm = do
  q <- punct ForAll <|> punct Exists
  vars <- bracks (sepBy1 binding (punct Comma))
  punct Colon
  rest <- unitaryTerm
  return (Quant q vars rest)

binding = do
  x <- var
  do { punct Colon; ty <- type_; return (Typed x ty) }
     <|> return (Untyped x)

type_ = fail "type_"

term = unitaryTerm `binExpr` (punct Or <|> punct And <|>
                              punct Iff <|> punct Implies <|>
                              punct Follows <|> punct Xor <|>
                              punct Nor <|> punct Nand)
