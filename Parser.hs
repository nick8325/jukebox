{-# LANGUAGE TypeSynonymInstances, MultiParamTypeClasses #-}
module Parser where

import Lexer hiding (Error, Type, Pos, keyword, defined)
import Formula hiding (kind, formula)
import qualified Lexer as L
import qualified Formula as F
import qualified Data.ByteString.Char8 as BS
import Parsimony hiding (Parser)
import Parsimony.Error
import Parsimony.Pos
import Parsimony.Stream hiding (Token)
import qualified Parsimony.Stream
import Parsimony.UserState
import Control.Monad
import qualified Data.Map as Map
import qualified Data.Set as Set

data IncludeStatement = Include BS.ByteString (Maybe [BS.ByteString])
data ParseState = MkState !(Problem Formula) !(Maybe [BS.ByteString])

type Parser = ParserU ParseState Contents

instance Parsimony.Stream.Token Token where
  updatePos = error "Parser.updatePos"
  showToken = show

instance Stream Contents Token where
  getToken (State Nil p) =
    Error $ newErrorMessage (UnExpect "end of input") p
  getToken (State (Cons t (At (L.Pos l c) ts)) p) =
    let p' = flip setSourceLine (fromIntegral l) $
             flip setSourceColumn (fromIntegral c) p in
    Ok t (State ts p')
  -- Note that, for example, the eof combinator will succeed when the
  -- token stream is in the error state! We detect this in the parser
  -- driver instead.
  getToken (State L.Error p) =
    Error $ newErrorMessage (UnExpect "lexical error") p

-- Primitive parsers.

satisfy p = try $ do
  t <- anyToken
  if p t then return t else unexpected (showToken t)
keyword' p = satisfy p'
  where p' Atom { L.keyword = k } = p k
        p' _ = False
keyword k = keyword' (== k) <?> show k
punct' p = satisfy p'
  where p' Punct { kind = k } = p k
        p' _ = False
punct k = punct' (== k) <?> show k
defined' p = satisfy p'
  where p' Defined { L.defined = d } = p d
        p' _ = False
defined k = defined' (== k) <?> show k
atom = keyword' (const True) <?> "atom"

-- Combinators.
parens p = between (punct LParen) (punct RParen) p
bracks p = between (punct LBrack) (punct RBrack) p
nested nest p = nest (nested nest p) <|> p -- e.g. nested parens p

-- Inserting types, predicates, functions and clauses.

newFormula :: Input Formula -> Parser ()
newFormula input = updateUserState (\(MkState x p) -> MkState x{ inputs = input:inputs x } p)

findType :: BS.ByteString -> Parser Type
findType name = do
  MkState s p <- getUserState
  case Map.lookup name (types s) of
    Nothing -> do
      let ty = Type { tname = name, tmonotone = Infinite, tsize = Infinite } 
      setUserState (MkState s{ types = Map.insert name ty (types s) } p)
      return ty
    Just x -> return x

findPredicate :: BS.ByteString -> [Type] -> Parser Predicate
findPredicate name args = do
  MkState s p <- getUserState
  case Map.lookup name (preds s) of
    Nothing -> do
      let pred = Predicate { pname = name }
      setUserState (MkState s{ preds = Map.insert name (args, pred) (preds s) } p)
      return pred
    Just (args', _) | args /= args' ->
      fail $ "Expected " ++ BS.unpack name ++ " to have type " ++ showPredType args ++
             " but it has type " ++ showPredType args'
    Just (_, pred) ->
      return pred

findFunction :: BS.ByteString -> [Type] -> Type -> Parser Function
findFunction name args res = do
  MkState s p <- getUserState
  case Map.lookup name (funs s) of
    Nothing -> do
      let fun = Function { fname = name, fres = res }
      setUserState (MkState s{ funs = Map.insert name (args, fun) (funs s) } p)
      return fun
    Just (args', fun) | args /= args' || res /= fres fun ->
      fail $ "Expected " ++ BS.unpack name ++ " to have type " ++ showFunType args res ++
             " but it has type " ++ showFunType args' (fres fun)
    Just (_, fun) ->
      return fun

-- Parsing formulae.

input :: Parser ()
input = declaration L.Type (keyword L.Type) (\_ _ -> typeDecl) <|>
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
               do { keyword L.NegatedConjecture; return (id, F.NegatedConjecture) }
        axiom k = do { keyword k; return (id, F.Axiom) }
        conjecture k = do { keyword k; return (nt, F.NegatedConjecture) }

declaration :: Keyword -> Parser a -> (BS.ByteString -> a -> Parser b) -> Parser b
declaration k p1 p2 = do
  keyword k
  res <- parens $ do
    Atom{name = tag} <- atom
    punct Comma
    kind <- p1
    punct Comma
    p2 tag kind
  punct Dot
  return res

typeDecl = nested parens $ do
  Atom{name = name} <- atom
  punct Colon
  let function = do
        lhs <- args
        punct FunArrow
        fun lhs
      constant = fun []
      fun lhs =
            do { defined DO; findPredicate name lhs; return () }
        <|> do { rhs <- type_; findFunction name lhs rhs; return () } 
      args = fmap concat (sepBy1 arg (punct Times))
        where arg = parens args <|>
                    do { ty <- type_; return [ty] }
      type_ =
            do { Atom { name = ty } <- atom; findType ty }
        <|> do { defined DI; findType individual }
 
  nested (try . parens) $ do { defined DTType; findType name; return () } <|>
                          try function <|>
                          constant

individual = BS.pack "$i"

cnf = fail "cnf"
tff = fail "tff"
fof = fail "fof"
