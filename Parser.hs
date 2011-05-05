{-# LANGUAGE TypeSynonymInstances, MultiParamTypeClasses #-}
module Parser where

import Lexer hiding (At, Error, Pos, Contents, Type, keyword, defined)
import qualified Lexer as L
import qualified Formula as F
import Formula hiding (kind, formula)
import Progress
import TPTP
import qualified Data.ByteString.Char8 as BS
import Text.Parsec hiding (Empty, Error, anyToken, token, satisfy)
import Text.Parsec.Error
import Text.Parsec.Pos
import qualified Control.Monad.Trans.Error as E
import Control.Monad.Trans.Class
import Control.Monad
import qualified Data.Map as Map
import qualified Data.Set as Set

-- The parser monad---boring stuff for interfacing between Alex and Parsec.

data Pos = MkPos FilePath {-# UNPACK #-} !L.Pos
data InputState = At {-# UNPACK #-} !Pos !Contents
data Contents = Empty | Error | Token !Token !TokenStream [(FilePath, TokenStream)]

type M = E.ErrorT Pos (Progress (TPTP IO)) -- ErrorT Pos is for reporting lex errors
type Parser = ParsecT InputState (Problem Formula) M

instance E.Error Pos where
  noMsg = error "instance Error Pos: not implemented"
  strMsg = error "instance Error Pos: not implemented"

instance Stream InputState M Token where
  uncons (At _ Empty) = return Nothing
  uncons (At pos Error) = E.throwError pos
  uncons (At (MkPos file _) (Token t ts xs)) = return (Just (t, nextState file ts xs))

{-# INLINE nextState #-}
nextState :: FilePath -> TokenStream -> [(FilePath, TokenStream)] -> InputState
nextState file (L.At pos Nil) xs = nextFile (MkPos file pos) xs
nextState file (L.At pos (Cons t ts)) xs = At (MkPos file pos) (Token t ts xs)
nextState file (L.At pos L.Error) _ = At (MkPos file pos) Error

{-# NOINLINE nextFile #-}
nextFile :: Pos -> [(FilePath, TokenStream)] -> InputState
nextFile pos [] = At pos Empty
nextFile _ ((file, ts):xs) = nextState file ts xs

sourcePos (MkPos file (L.Pos l c)) = newPos file (fromIntegral l) (fromIntegral c)

-- countTokens :: Parser Int
-- countTokens = skipMany (satisfy (isAtom (== Fof)) >> satisfy (isPunct LParen) >> satisfy (isAtom (const True)) >> satisfy (isPunct Comma) >> ((satisfy (isAtom (== Conjecture)) >> skipMany brackets) <|> (satisfy (isAtom (== Axiom)) >> skipMany brackets)) >> satisfy (isPunct RParen) >> satisfy (isPunct Dot)) >> eof >> getState
--   where isPunct k Punct{kind=k'} = k == k'
--         isPunct k _ = False
--         isAtom p Atom{keyword=k} = p k
--         isAtom p _ = False
--         kind k = k == Conjecture || k == Axiom
--         brackets = (satisfy (isPunct LParen) >> modifyState (+1) >> skipMany brackets >> satisfy (isPunct RParen)) <|>
--                    (satisfy (not . isPunct RParen))

runParser :: Parser a -> FilePath -> TokenStream -> IO (Either ParseError a)
runParser p file ts = do
  let state@(At pos _) = nextState file ts []
      errorT = runParserT (setPosition (sourcePos pos) >> p) (Problem Map.empty Map.empty Map.empty []) file state
      progress = E.runErrorT errorT
      tptp = runProgress progress 100000 $ "Parsing " ++ file ++ ".."
      io = runTPTP tptp (const (return Nothing))
  res <- io
  case res of
    Left pos ->
      return (Left (newErrorMessage (Message "lexical error") (sourcePos pos)))
    Right x ->
      return x

-- Primitive parsers.

token :: (Token -> Maybe a) -> Parser a
token f = lift (lift tick) >> tokenPrim show (\_ _ (At pos _) -> sourcePos pos) f

anyToken = token Just
satisfy p = token (\x -> if p x then Just x else Nothing)
keyword p = satisfy p'
  where p' Atom { L.keyword = k } = p k
        p' _ = False
punct p = satisfy p'
  where p' Punct { kind = k } = p k
        p' _ = False
defined p = satisfy p'
  where p' Defined { L.defined = d } = p d
        p' _ = False
atom = keyword (const True)
parens p = between (punct (== LParen)) (punct (== RParen)) p
bracks p = between (punct (== LBrack)) (punct (== RBrack)) p
nested nest p = nest (nested nest p) <|> p -- e.g. nested parens p

-- Inserting types, predicates, functions and clauses.

newFormula :: Input Formula -> Parser ()
newFormula input = modifyState (\x -> x { inputs = input:inputs x })

findType :: BS.ByteString -> Parser Type
findType name = do
  s <- getState
  case Map.lookup name (types s) of
    Nothing -> do
      let ty = Type { tname = name, tmonotone = Infinite, tsize = Infinite } 
      putState s { types = Map.insert name ty (types s) }
      return ty
    Just x -> return x

findPredicate :: BS.ByteString -> [Type] -> Parser Predicate
findPredicate name args = do
  s <- getState
  case Map.lookup name (preds s) of
    Nothing -> do
      let pred = Predicate { pname = name }
      putState s { preds = Map.insert name (args, pred) (preds s) }
      return pred
    Just (args', _) | args /= args' ->
      fail $ "Expected " ++ BS.unpack name ++ " to have type " ++ showPredType args ++
             " but it has type " ++ showPredType args'
    Just (_, pred) ->
      return pred

findFunction :: BS.ByteString -> [Type] -> Type -> Parser Function
findFunction name args res = do
  s <- getState
  case Map.lookup name (funs s) of
    Nothing -> do
      let fun = Function { fname = name, fres = res }
      putState s { funs = Map.insert name (args, fun) (funs s) }
      return fun
    Just (args', fun) | args /= args' || res /= fres fun ->
      fail $ "Expected " ++ BS.unpack name ++ " to have type " ++ showFunType args res ++
             " but it has type " ++ showFunType args' (fres fun)
    Just (_, fun) ->
      return fun

-- Parsing formulae.

problem :: Parser (Problem Formula)
problem = do
  many input
  x <- getState
  return x { inputs = reverse (inputs x) }

input :: Parser ()
input = declaration L.Type (keyword (== L.Type)) (\_ _ -> typeDecl) <|>
        formula Cnf cnf <|>
        formula Tff tff <|>
        formula Fof fof
  where formula k p = declaration k kind $
                        \tag (f, kind) -> do
                          res <- p
                          newFormula Input{ F.kind = kind, tag = tag, F.formula = f res }
        kind = axiom L.Axiom <|> 
               axiom L.Hypothesis <|>
               axiom L.Definition <|>
               axiom L.Assumption <|>
               axiom L.Lemma <|>
               axiom L.Theorem <|>
               conjecture L.Conjecture <|>
               conjecture L.Question <|>
               do { keyword (== L.NegatedConjecture); return (id, F.NegatedConjecture) }
        axiom k = do { keyword (== k); return (id, F.Axiom) }
        conjecture k = do { keyword (== k); return (nt, F.NegatedConjecture) }

declaration :: Keyword -> Parser a -> (BS.ByteString -> a -> Parser b) -> Parser b
declaration k p1 p2 = do
  keyword (== k)
  res <- parens $ do
    Atom{name = tag} <- atom
    punct (== Comma)
    kind <- p1
    punct (== Comma)
    p2 tag kind
  punct (== Dot)
  return res

typeDecl = nested parens $ do
  Atom{name = name} <- atom
  punct (== Colon)
  let function = do
        lhs <- args
        punct (== FunArrow)
        fun lhs
      constant = fun []
      fun lhs =
            do { defined (== DO); findPredicate name lhs; return () }
        <|> do { rhs <- type_; findFunction name lhs rhs; return () } 
      args = fmap concat (sepBy1 arg (punct (== Times)))
        where arg = parens args <|>
                    do { ty <- type_; return [ty] }
      type_ =
            do { Atom { name = ty } <- atom; findType ty }
        <|> do { defined (== DI); findType individual }
 
  nested (try . parens) $ do { defined (== DTType); findType name; return () } <|>
                          try function <|>
                          constant

individual = BS.pack "$i"

cnf = fail "cnf"
tff = fail "tff"
fof = fail "fof"
