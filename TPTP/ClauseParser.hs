-- Parse and typecheck TPTP clauses, stopping at include-clauses.

{-# LANGUAGE BangPatterns, MultiParamTypeClasses, ImplicitParams #-}
module TPTP.ClauseParser where

import Text.Parsec hiding (satisfy, eof, token, runParser)
import Text.Parsec.Error
import Text.Parsec.Pos
import Text.Parsec.Prim hiding (runParser, token)
import Control.Monad.Identity
import qualified Data.ByteString.Lazy.Char8 as BSL
import qualified Data.ByteString.Char8 as BS
import qualified Data.Map as Map
import Data.Map(Map)
import qualified Data.Set as Set
import qualified AppList
import Data.List
import TPTP.Print

import TPTP.Lexer hiding
  (At, Error, Include, Pos, Var, Type, Not, ForAll,
   Exists, And, Or, Type, Apply, keyword, defined, kind)
import qualified TPTP.Lexer as L
import qualified Formula
import Formula hiding (tag, kind, formula, Axiom, NegatedConjecture)

-- The parser monad

data ParseState =
  MkState !(Problem Formula) -- problem being constructed, inputs are in reverse order
          !(Maybe Type)      -- the $i type, if used in the problem
          !(Maybe [Tag])     -- only clauses with these names are added to the problem
  deriving Show
type Parser = Parsec Contents ParseState
type ParsecState = State Contents ParseState

-- An include-clause.
data IncludeStatement = Include BS.ByteString (Maybe [Tag]) deriving Show

instance Stream Contents Identity Token where
  -- dummy instance---we have our own combinators for fetching from
  -- the stream, since parsec struggles with our special Error token.
  uncons = error "uncons: not implemented"

-- The initial Parsec state.
openFile :: FilePath -> TokenStream -> ParsecState
openFile file (L.At (L.Pos l c) ts) = State ts pos state0
  where pos = newPos file (fromIntegral l) (fromIntegral c)
        state0 = MkState (Problem Map.empty Map.empty Map.empty []) Nothing Nothing

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

getProblem :: Parser (Problem Formula)
getProblem = do
  MkState p _ _ <- getState
  return p { inputs = reverse (inputs p) }

-- Primitive parsers.

satisfy p = mkPT $ \s ->
  let err c msg = Identity (c (Identity (Error (newErrorMessage msg (statePos s))))) in
  case stateInput s of
    Nil -> err Empty (UnExpect "end of input")
    Cons t (L.At (L.Pos l c) !ts) ->
      if p t
         then let !pos' = flip setSourceLine (fromIntegral l) .
                          flip setSourceColumn (fromIntegral c) $ statePos s
                  !s' = s { statePos = pos', stateInput = ts }
              in Identity (Consumed (Identity (Ok t s' (unknownError s'))))
         else err Empty (UnExpect ("'" ++ prettyShow t ++ "'"))
    L.Error -> err Consumed (Message "lexical error")

-- Opposite of 'try'.
consume p = mkPT $ \s ->
  case runParsecT p s of
    Identity (Empty x) -> Identity (Consumed x)
    Identity (Consumed x) -> Identity (Consumed x)

eof = notFollowedBy (satisfy (const True)) <?> "end of input"

keyword' p = satisfy p'
  where p' Atom { L.keyword = k } = p k
        p' _ = False
keyword k = keyword' (== k) <?> "'" ++ show k ++ "'"
punct' p = satisfy p'
  where p' Punct { L.kind = k } = p k
        p' _ = False
punct k = punct' (== k) <?> "'" ++ show k ++ "'"
defined' p = fmap L.defined (satisfy p')
  where p' Defined { L.defined = d } = p d
        p' _ = False
defined k = defined' (== k) <?> "'" ++ show k ++ "'"
variable = fmap name (satisfy p) <?> "variable"
  where p L.Var{} = True
        p _ = False
number = fmap value (satisfy p) <?> "number"
  where p Number{} = True
        p _ = False
atom = fmap name (keyword' (const True)) <?> "atom"

-- Combinators.

parens, bracks :: Parser a -> Parser a
parens p = between (punct LParen) (punct RParen) p
bracks p = between (punct LBrack) (punct RBrack) p

-- Build an expression parser from a binary-connective parser
-- and a leaf parser.
binExpr :: Parser a -> Parser (a -> a -> Parser a) -> Parser a
binExpr leaf op = do
  lhs <- leaf
  do { f <- op; rhs <- binExpr leaf op; f lhs rhs } <|> return lhs

-- Parsing clauses.

-- Parse as many things as possible until EOF or an include statement.
section :: Parser (Maybe IncludeStatement)
section = skipMany input >> (fmap Just include <|> (eof >> return Nothing))

-- A single non-include clause.
input :: Parser ()
input = declaration Cnf (formulaIn cnf) <|>
        declaration Fof (formulaIn fof) <|>
        declaration Tff (\tag -> formulaIn tff tag <|> typeDeclaration)
  where declaration k m = do
          keyword k
          parens $ do
            t <- tag
            punct Comma
            -- Don't bother typechecking clauses that we are not
            -- supposed to include in the problem (seems in the
            -- spirit of TPTP's include mechanism)
            b <- included t
            if b then m t else balancedParens
          punct Dot
          return ()
        formulaIn lang tag = do
          k <- kind
          punct Comma
          form <- lang
          newFormula (k tag form)
        -- Relies on Parsec's non-backtracking behaviour
        balancedParens = parens balancedParens <|> (satisfy (const True) >> balancedParens)
        included t = do
          MkState _ _ x <- getState
          case x of
            Nothing -> return True
            Just ts -> return (t `elem` ts)

-- A TPTP kind.
kind :: Parser (Tag -> Formula -> Input Formula)
kind = axiom Axiom <|> axiom Hypothesis <|> axiom Definition <|>
       axiom Assumption <|> axiom Lemma <|> axiom Theorem <|>
       general Conjecture Formula.NegatedConjecture Not <|>
       general NegatedConjecture Formula.NegatedConjecture id <|>
       general Question Formula.NegatedConjecture Not
  where axiom t = general t Formula.Axiom id
        general k kind f = keyword k >> return (mk kind f)
        mk kind f tag form =
          Input { Formula.tag = tag,
                  Formula.kind = kind,
                  Formula.formula = f form }

-- A formula name.
tag :: Parser Tag
tag = atom <|> fmap (BS.pack . show) number <?> "clause name"

-- An include declaration.
include :: Parser IncludeStatement
include = do
  keyword L.Include
  res <- parens $ do
    name <- atom <?> "quoted filename"
    clauses <- do { punct Comma
                  ; fmap Just (bracks (sepBy1 tag (punct Comma))) } <|> return Nothing
    return (Include name clauses)
  punct Dot
  return res

-- Inserting types, predicates, functions and clauses.

newFormula :: Input Formula -> Parser ()
newFormula input = do
  MkState x i p <- getState
  putState (MkState x{ inputs = input:inputs x } i p)

findType :: BS.ByteString -> Parser Type
findType name = do
  MkState s i p <- getState
  case Map.lookup name (types s) of
    Nothing -> do
      let ty = Type { tname = name, tmonotone = Infinite, tsize = Infinite } 
      putState (MkState s{ types = Map.insert name ty (types s) } i p)
      return ty
    Just x -> return x

findPredicate :: BS.ByteString -> [Type] -> Parser Predicate
findPredicate name args = do
  MkState s i p <- getState
  case Map.lookup name (preds s) of
    Nothing -> do
      let pred = Predicate { pname = name }
      putState (MkState s{ preds = Map.insert name (args, pred) (preds s) } i p)
      return pred
    Just (args', _) | args /= args' ->
      fail $ "Predicate " ++ BS.unpack name ++ " was used at type " ++ showPredType args ++
             " but it has type " ++ showPredType args'
    Just (_, pred) ->
      return pred

findFunction :: BS.ByteString -> [Type] -> Parser Function
findFunction name args = do
  MkState s i p <- getState
  case Map.lookup name (funs s) of
    Nothing -> do
      ind <- individual
      let fun = Function { fname = name, fres = ind }
      putState (MkState s{ funs = Map.insert name (args, fun) (funs s) } i p)
      return fun
    Just (args', fun) | args /= args' ->
      fail $ "Function " ++ BS.unpack name ++ " was used at argument type " ++ showArgs args ++
             " but its type is " ++ showFunType args' (fres fun)
    Just (_, fun) ->
      return fun

newFunction :: BS.ByteString -> [Type] -> Type -> Parser Function
newFunction name args res = do
  MkState s i p <- getState
  case Map.lookup name (funs s) of
    Nothing -> do
      let fun = Function { fname = name, fres = res }
      putState (MkState s{ funs = Map.insert name (args, fun) (funs s) } i p)
      return fun
    Just (args', fun) | args /= args' || res /= fres fun ->
      fail $ "Function " ++ BS.unpack name ++ " was declared to have type " ++ showFunType args res ++
             " but it already has type " ++ showFunType args' (fres fun)
    Just (_, fun) ->
      return fun

-- The type $i (anything whose type is not specified gets this type)
individual :: Parser Type
individual = do
  MkState x i p <- getState
  case i of
    Nothing -> do
      ind <- findType (BS.pack "$i")
      putState (MkState x (Just ind) p)
      return ind
    Just x -> return x

-- Parsing formulae.

cnf, tff, fof :: Parser Formula
cnf = fail "cnf not implemented"
tff =
  let ?binder = varDecl True
      ?ctx = Map.empty
  in formula
fof =
  let ?binder = varDecl False
      ?ctx = Map.empty
  in formula

-- We cannot always know whether what we are parsing is a formula or a
-- term, since we don't have lookahead. For example, p(x) might be a
-- formula, but in p(x)=y, p(x) is a term.
--
-- To deal with this, we introduce the Thing datatype.
-- A thing is either a term or a formula, or a literal that we don't know
-- if it should be a term or a formula. Instead of a separate formula-parser
-- and term-parser we have a combined thing-parser.
data Thing = Apply !BS.ByteString ![Term] | Term !Term | Formula !Formula

-- However, often we do know whether we want a formula or a term,
-- and there it's best to use a specialised parser (not least because
-- the error messages are better). For that reason, our parser is
-- parametrised on the type of thing you want to parse. We have two
-- main parsers:
--   * 'term' parses an atomic expression
--   * 'formula' parses an arbitrary expression
-- You can instantiate 'term' for Term, Formula or Thing; in each case
-- you get an appropriate parser. You can instantiate 'formula' for
-- Formula or Thing.

-- Types for which a term f(...) is a valid literal. These are the types on
-- which you can use 'term'.
class TermLike a where
  -- Convert from a Thing.
  fromThing :: Thing -> Parser a
  -- Parse a variable occurrence as a term on its own, if that's allowed.
  var :: (?ctx :: Map BS.ByteString Variable) => Parser a
  -- A parser for this type.
  parser :: (?binder :: Parser Variable, ?ctx :: Map BS.ByteString Variable) => Parser a

instance TermLike Formula where
  fromThing (Apply x xs) = do
    f <- findPredicate x (map ty xs)
    return (Literal (Pos (f :?: xs)))
  fromThing (Term _) = mzero
  fromThing (Formula f) = return f
  -- A variable itself is not a valid formula.
  var = mzero
  parser = formula

instance TermLike Term where
  fromThing (Apply x xs) = do
    f <- findFunction x (map ty xs)
    return (f :@: xs)
  fromThing (Term t) = return t
  fromThing (Formula _) = mzero
  parser = term
  var = do
    x <- variable
    case Map.lookup x ?ctx of
      Just v -> return (Var v)
      Nothing -> fail $ "unbound variable " ++ BS.unpack x

instance TermLike Thing where
  fromThing = return
  var = fmap Term var
  parser = formula

-- Types that can represent formulae. These are the types on which
-- you can use 'formula'.
class TermLike a => FormulaLike a where fromFormula :: Formula -> a
instance FormulaLike Formula where fromFormula = id
instance FormulaLike Thing where fromFormula = Formula

-- An atomic expression.
term :: (?binder :: Parser Variable, ?ctx :: Map BS.ByteString Variable, TermLike a) => Parser a
term = function <|> var <|> parens parser <?> "term"
  where function = do
          x <- atom
          args <- parens (sepBy1 term (punct Comma)) <|> return []
          fromThing (Apply x args)

literal, unitary, quantified, formula ::
  (?binder :: Parser Variable, ?ctx :: Map BS.ByteString Variable, FormulaLike a) => Parser a
literal = true <|> false <|> binary <?> "literal"
  where true = do { defined DTrue; return (fromFormula (And AppList.Nil)) }
        false = do { defined DFalse; return (fromFormula (Or AppList.Nil)) }
        binary = do
          x <- term :: Parser Thing
          let f p sign = do
               lhs <- fromThing x :: Parser Term
               punct p
               rhs <- term :: Parser Term
               when (ty lhs /= ty rhs) $
                 fail $ "Type mismatch in equality: left hand side has type " ++ prettyShow (ty lhs) ++ " and right hand side has type " ++ prettyShow (ty rhs)
               return (fromFormula . Literal . sign $ lhs :=: rhs)
          f Eq Pos <|> f Neq Neg <|> fromThing x

unitary = negation <|> quantified <|> literal
  where negation = do
          punct L.Not
          fmap (fromFormula . Not) (unitary :: Parser Formula)

quantified = do
  q <- (punct L.ForAll >> return ForAll) <|>
       (punct L.Exists >> return Exists)
  vars <- bracks (sepBy1 ?binder (punct Comma))
  let ctx' = foldl' (\m v -> Map.insert (vname v) v m) ?ctx vars
  punct Colon
  rest <- let ?ctx = ctx' in (unitary :: Parser Formula)
  return (fromFormula (q (Set.fromList vars) rest))

-- A general formula.
formula = do
  x <- unitary :: Parser Thing
  let binop op t u = op (AppList.Unit t `AppList.append` AppList.Unit u)
      connective p op = do
        lhs <- fromThing x
        punct p
        rhs <- formula :: Parser Formula
        return (fromFormula (op lhs rhs))
  connective L.And (binop And) <|> connective L.Or (binop Or) <|>
   connective Iff Equiv <|>
   connective Implies (\t u -> binop Or (Not t) u) <|>
   connective Follows (\t u -> binop Or t (Not u)) <|>
   connective Xor (\t u -> Not (t `Equiv` u)) <|>
   connective Nor (\t u -> Not (binop Or t u)) <|>
   connective Nand (\t u -> Not (binop And t u)) <|>
   fromThing x

-- varDecl True: parse a typed variable binding X:a or an untyped one X
-- varDecl Fals: parse an untyped variable binding X
varDecl :: Bool -> Parser Variable
varDecl typed = do
  x <- variable
  ty <- do { punct Colon;
             when (not typed) $
               fail "Used a typed quantification in an untyped formula";
             type_ } <|> individual
  return Variable { vname = x, vtype = ty }

-- Parse a type
type_ :: Parser Type
type_ =
  do { name <- atom; findType name } <|>
  do { defined DI; individual }

-- A little data type to help with parsing types.
data Type_ = TType | O | Fun [Type] Type | Pred [Type] | Prod [Type]

prod :: Type_ -> Type_ -> Parser Type_
prod (Prod tys) (Prod tys2) = return $ Prod (tys ++ tys2)
prod _ _ = fail "invalid type"

arrow :: Type_ -> Type_ -> Parser Type_
arrow (Prod ts) (Prod [x]) = return $ Fun ts x
arrow (Prod ts) O = return $ Pred ts
arrow _ _ = fail "invalid type"

leaf :: Parser Type_
leaf = do { defined DTType; return TType } <|>
       do { defined DO; return O } <|>
       do { ty <- type_; return (Prod [ty]) } <|>
       parens compoundType

compoundType :: Parser Type_
compoundType = leaf `binExpr` (punct Times >> return prod)
                    `binExpr` (punct FunArrow >> return arrow)

typeDeclaration :: Parser ()
typeDeclaration = do
  keyword L.Type
  punct Comma
  let manyParens p = parens (manyParens p) <|> p
  manyParens $ do
    name <- atom
    punct Colon
    res <- compoundType
    case res of
      TType -> do { findType name; return () }
      O -> do { findPredicate name []; return () }
      Fun args res -> do { newFunction name args res; return () }
      Pred args -> do { findPredicate name args; return () }
      Prod [res] -> do { newFunction name [] res; return () }
      _ -> fail "invalid type"
