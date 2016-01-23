-- Parse and typecheck TPTP clauses, stopping at include-clauses.

{-# LANGUAGE BangPatterns, MultiParamTypeClasses, ImplicitParams, FlexibleInstances, TypeOperators, TypeFamilies #-}
{-# OPTIONS_GHC -funfolding-use-threshold=1000 #-}
module Jukebox.TPTP.ClauseParser where

import Jukebox.TPTP.Parsec
import Control.Applicative
import Control.Monad
import qualified Data.Map.Strict as Map
import Data.Map(Map)
import Data.List
import Jukebox.TPTP.Print
import Jukebox.Name
import qualified Data.Set as Set
import Data.Int

import Jukebox.TPTP.Lexer hiding
  (Pos, Error, Include, Var, Type, Not, ForAll,
   Exists, And, Or, Type, Apply, Implies, Follows, Xor, Nand, Nor,
   keyword, defined, kind)
import qualified Jukebox.TPTP.Lexer as L
import qualified Jukebox.Form as Form
import Jukebox.Form hiding (tag, kind, Axiom, Conjecture, Question, newFunction, TypeOf(..), run)
import qualified Jukebox.Name as Name

-- The parser monad

data ParseState =
  MkState ![Input Form]                    -- problem being constructed, inputs are in reverse order
          !(Map String (Name ::: FunType)) -- functions in scope
type Parser = Parsec ParsecState
type ParsecState = UserState ParseState TokenStream

-- An include-clause.
data IncludeStatement = Include String (Maybe [Tag]) deriving Show

-- The initial parser state.
initialState :: ParseState
initialState = MkState [] Map.empty

instance Stream TokenStream Token where
  primToken (At _ (Cons Eof _)) ok err fatal = err
  primToken (At _ (Cons L.Error _)) ok err fatal = fatal "Lexical error"
  primToken (At _ (Cons t ts)) ok err fatal = ok ts t
  type Position TokenStream = TokenStream
  position = id

-- Wee function for testing.
testParser :: Parser a -> String -> Either [String] a
testParser p s = snd (run (const []) p (UserState initialState (scan s)))

getProblem :: Parser [Input Form]
getProblem = do
  MkState p _ <- getState
  return (reverse p)

-- Primitive parsers.

{-# INLINE keyword' #-}
keyword' p = satisfy p'
  where p' Atom { L.keyword = k } = p k
        p' _ = False
{-# INLINE keyword #-}
keyword k = keyword' (== k) <?> "'" ++ show k ++ "'"
{-# INLINE punct' #-}
punct' p = satisfy p'
  where p' Punct { L.kind = k } = p k
        p' _ = False
{-# INLINE punct #-}
punct k = punct' (== k) <?> "'" ++ show k ++ "'"
{-# INLINE defined' #-}
defined' p = fmap L.defined (satisfy p')
  where p' Defined { L.defined = d } = p d
        p' _ = False
{-# INLINE defined #-}
defined k = defined' (== k) <?> "'" ++ show k ++ "'"
{-# INLINE variable #-}
variable = fmap tokenName (satisfy p) <?> "variable"
  where p L.Var{} = True
        p _ = False
{-# INLINE number #-}
number = fmap value (satisfy p) <?> "number"
  where p Number{} = True
        p _ = False
{-# INLINE atom #-}
atom = fmap tokenName (keyword' (const True)) <?> "atom"

-- Combinators.

parens, bracks :: Parser a -> Parser a
{-# INLINE parens #-}
parens p = between (punct LParen) (punct RParen) p
{-# INLINE bracks #-}
bracks p = between (punct LBrack) (punct RBrack) p

-- Build an expression parser from a binary-connective parser
-- and a leaf parser.
binExpr :: Parser a -> Parser (a -> a -> Parser a) -> Parser a
binExpr leaf op = do
  lhs <- leaf
  do { f <- op; rhs <- binExpr leaf op; f lhs rhs } <|> return lhs

-- Parsing clauses.

-- Parse as many things as possible until EOF or an include statement.
section :: (Tag -> Bool) -> Parser (Maybe IncludeStatement)
section included = skipMany (input included) >> (fmap Just include <|> (eof >> return Nothing))

-- A single non-include clause.
input :: (Tag -> Bool) -> Parser ()
input included = declaration Cnf (formulaIn cnf) <|>
                 declaration Fof (formulaIn fof) <|>
                 declaration Tff (\tag -> formulaIn tff tag <|> typeDeclaration)
  where {-# INLINE declaration #-}
        declaration k m = do
          keyword k
          parens $ do
            t <- tag
            punct Comma
            -- Don't bother typechecking clauses that we are not
            -- supposed to include in the problem (seems in the
            -- spirit of TPTP's include mechanism)
            if included t then m t else balancedParens
          punct Dot
          return ()
        formulaIn lang tag = do
          k <- kind
          punct Comma
          form <- lang
          newFormula (k tag form)
        balancedParens = skipMany (parens balancedParens <|> (satisfy p >> return ()))
        p Punct{L.kind=LParen} = False
        p Punct{L.kind=RParen} = False
        p _ = True

-- A TPTP kind.
kind :: Parser (Tag -> Form -> Input Form)
kind = axiom Axiom <|> axiom Hypothesis <|> axiom Definition <|>
       axiom Assumption <|> axiom Lemma <|> axiom Theorem <|>
       general Conjecture Form.Conjecture <|>
       general NegatedConjecture Form.Axiom <|>
       general Question Form.Question
  where axiom t = general t Form.Axiom
        general k kind = keyword k >> return (mk kind)
        mk kind tag form =
          Input { Form.tag = tag,
                  Form.kind = kind,
                  Form.what = form }

-- A formula name.
tag :: Parser Tag
tag = atom <|> fmap show number <?> "clause name"

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

-- Inserting types, functions and clauses.

newFormula :: Input Form -> Parser ()
newFormula input = do
  MkState p f <- getState
  putState (MkState (input:p) f)
  
newFunction :: String -> FunType -> Parser (Name ::: FunType)
newFunction name ty' = do
  f@(_ ::: ty) <- lookupFunction ty' name
  unless (ty == ty') $ do
    fatalError $ "Constant " ++ name ++
                 " was declared to have type " ++ prettyShow ty' ++
                 " but already has type " ++ prettyShow ty
  return f

{-# INLINE applyFunction #-}
applyFunction :: String -> [Term] -> Type -> Parser Term
applyFunction name args' res = do
  f@(_ ::: ty) <- lookupFunction (FunType (replicate (length args') individual) res) name
  unless (map typ args' == args ty) $ typeError f args'
  return (f :@: args')

{-# NOINLINE typeError #-}
typeError f@(x ::: ty) args' = do
    let plural 1 x y = x 
        plural _ x y = y
    fatalError $ "Type mismatch in term '" ++ prettyShow (f :@: args') ++ "': " ++
                 "Constant " ++ prettyShow x ++
                 if length (args ty) == length args' then
                   " has type " ++ prettyShow ty ++
                   " but was applied to " ++ plural (length args') "an argument" "arguments" ++
                   " of type " ++ prettyShow (map typ args')
                 else
                   " has arity " ++ show (length args') ++
                   " but was applied to " ++ show (length (args ty)) ++
                   plural (length (args ty)) " argument" " arguments"

{-# INLINE lookupFunction #-}
lookupFunction :: FunType -> String -> Parser (Name ::: FunType)
lookupFunction def x = do
  MkState p f <- getState
  case Map.lookup x f of
    Nothing -> do
      let decl = name x ::: def
      putState (MkState p (Map.insert x decl f))
      return decl
    Just f -> return f

-- The type $i (anything whose type is not specified gets this type)
individual :: Type
individual = Type (name "$i") Infinite Infinite

-- Parsing formulae.

cnf, tff, fof :: Parser Form
cnf =
  let ?binder = fatalError "Can't use quantifiers in CNF"
      ?ctx = Nothing
  in fmap (ForAll . bind) formula
tff =
  let ?binder = varDecl True
      ?ctx = Just Map.empty
  in formula
fof =
  let ?binder = varDecl False
      ?ctx = Just Map.empty
  in formula

-- We cannot always know whether what we are parsing is a formula or a
-- term, since we don't have lookahead. For example, p(x) might be a
-- formula, but in p(x)=y, p(x) is a term.
--
-- To deal with this, we introduce the Thing datatype.
-- A thing is either a term or a formula, or a literal that we don't know
-- if it should be a term or a formula. Instead of a separate formula-parser
-- and term-parser we have a combined thing-parser.
data Thing = Apply !String ![Term]
           | Term !Term
           | Formula !Form

instance Show Thing where
  show (Apply f []) = f
  show (Apply f args) =
    f ++
      case args of
        [] -> ""
        args -> prettyShow args
  show (Term t) = prettyShow t
  show (Formula f) = prettyShow f

-- However, often we do know whether we want a formula or a term,
-- and there it's best to use a specialised parser (not least because
-- the error messages are better). For that reason, our parser is
-- parametrised on the type of thing you want to parse. We have two
-- main parsers:
--   * 'term' parses an atomic expression
--   * 'formula' parses an arbitrary expression
-- You can instantiate 'term' for Term, Form or Thing; in each case
-- you get an appropriate parser. You can instantiate 'formula' for
-- Form or Thing.

-- Types for which a term f(...) is a valid literal. These are the types on
-- which you can use 'term'.
class TermLike a where
  -- Convert from a Thing.
  fromThing :: Thing -> Parser a
  -- Parse a variable occurrence as a term on its own, if that's allowed.
  var :: (?ctx :: Maybe (Map String Variable)) => Parser a
  -- A parser for this type.
  parser :: (?binder :: Parser Variable,
             ?ctx :: Maybe (Map String Variable)) => Parser a

instance TermLike Form where
  {-# INLINE fromThing #-}
  fromThing t@(Apply x xs) = fmap (Literal . Pos . Tru) (applyFunction x xs O)
  fromThing (Term _) = mzero
  fromThing (Formula f) = return f
  -- A variable itself is not a valid formula.
  var = mzero
  parser = formula

instance TermLike Term where
  {-# INLINE fromThing #-}
  fromThing t@(Apply x xs) = applyFunction x xs individual
  fromThing (Term t) = return t
  fromThing (Formula _) = mzero
  parser = term
  var = do
    x <- variable
    case ?ctx of
      Nothing ->
        return (Var (name x ::: individual))
      Just ctx ->
        case Map.lookup x ctx of
          Just v -> return (Var v)
          Nothing -> fatalError $ "unbound variable " ++ x

instance TermLike Thing where
  fromThing = return
  var = fmap Term var
  parser = formula

-- Types that can represent formulae. These are the types on which
-- you can use 'formula'.
class TermLike a => FormulaLike a where
  fromFormula :: Form -> a
instance FormulaLike Form where fromFormula = id
instance FormulaLike Thing where fromFormula = Formula

-- An atomic expression.
{-# SPECIALISE term :: (?binder :: Parser Variable, ?ctx :: Maybe (Map String Variable)) => Parser Term #-}
{-# SPECIALISE term :: (?binder :: Parser Variable, ?ctx :: Maybe (Map String Variable)) => Parser Form #-}
{-# SPECIALISE term :: (?binder :: Parser Variable, ?ctx :: Maybe (Map String Variable)) => Parser Thing #-}
term :: (?binder :: Parser Variable, ?ctx :: Maybe (Map String Variable), TermLike a) => Parser a
term = function <|> var <|> parens parser
  where {-# INLINE function #-}
        function = do
          x <- atom
          args <- parens (sepBy1 term (punct Comma)) <|> return []
          fromThing (Apply x args)

literal, unitary, quantified, formula ::
  (?binder :: Parser Variable, ?ctx :: Maybe (Map String Variable), FormulaLike a) => Parser a
{-# INLINE literal #-}
literal = true <|> false <|> binary <?> "literal"
  where {-# INLINE true #-}
        true = do { defined DTrue; return (fromFormula (And [])) }
        {-# INLINE false #-}
        false = do { defined DFalse; return (fromFormula (Or [])) }
        binary = do
          x <- term :: Parser Thing
          let {-# INLINE f #-}
              f p sign = do
               punct p
               lhs <- fromThing x :: Parser Term
               rhs <- term :: Parser Term
               let form = Literal . sign $ lhs :=: rhs
               when (typ lhs /= typ rhs) $
                 fatalError $ "Type mismatch in equality '" ++ prettyShow form ++ 
                              "': left hand side has type " ++ prettyShow (typ lhs) ++
                              " but right hand side has type " ++ prettyShow (typ rhs)
               return (fromFormula form)
          f Eq Pos <|> f Neq Neg <|> fromThing x

{-# SPECIALISE unitary :: (?binder :: Parser Variable, ?ctx :: Maybe (Map String Variable)) => Parser Form #-}
{-# SPECIALISE unitary :: (?binder :: Parser Variable, ?ctx :: Maybe (Map String Variable)) => Parser Thing #-}
unitary = negation <|> quantified <|> literal
  where {-# INLINE negation #-}
        negation = do
          punct L.Not
          fmap (fromFormula . Not) (unitary :: Parser Form)

{-# INLINE quantified #-}
quantified = do
  q <- (punct L.ForAll >> return ForAll) <|>
       (punct L.Exists >> return Exists)
  vars <- bracks (sepBy1 ?binder (punct Comma))
  let Just ctx = ?ctx
      ctx' = foldl' (\m v -> Map.insert (Name.base (Name.name v)) v m) ctx vars
  punct Colon
  rest <- let ?ctx = Just ctx' in (unitary :: Parser Form)
  return (fromFormula (q (Bind (Set.fromList vars) rest)))

-- A general formula.
{-# SPECIALISE formula :: (?binder :: Parser Variable, ?ctx :: Maybe (Map String Variable)) => Parser Form #-}
{-# SPECIALISE formula :: (?binder :: Parser Variable, ?ctx :: Maybe (Map String Variable)) => Parser Thing #-}
formula = do
  x <- unitary :: Parser Thing
  let binop op t u = op [t, u]
      {-# INLINE connective #-}
      connective p op = do
        punct p
        lhs <- fromThing x
        rhs <- formula :: Parser Form
        return (fromFormula (op lhs rhs))
  connective L.And (binop And) <|> connective L.Or (binop Or) <|>
   connective Iff Equiv <|>
   connective L.Implies (Connective Implies) <|>
   connective L.Follows (Connective Follows) <|>
   connective L.Xor (Connective Xor) <|>
   connective L.Nor (Connective Nor) <|>
   connective L.Nand (Connective Nand) <|>
   fromThing x

-- varDecl True: parse a typed variable binding X:a or an untyped one X
-- varDecl False: parse an untyped variable binding X
varDecl :: Bool -> Parser Variable
varDecl typed = do
  x <- variable
  ty <- do { punct Colon;
             when (not typed) $
               fatalError "Used a typed quantification in an untyped formula";
             type_ } <|> return individual
  return (name x ::: ty)

-- Parse a type
type_ :: Parser Type
type_ =
  do { x <- atom; return (Type (name x) Infinite Infinite) } <|>
  do { defined DI; return individual }

-- A little data type to help with parsing types.
data Type_ = TType | Fun [Type] Type | Prod [Type]

prod :: Type_ -> Type_ -> Parser Type_
prod (Prod tys) (Prod tys2) | not (O `elem` tys ++ tys2) = return $ Prod (tys ++ tys2)
prod _ _ = fatalError "invalid type"

arrow :: Type_ -> Type_ -> Parser Type_
arrow (Prod ts) (Prod [x]) = return $ Fun ts x
arrow _ _ = fatalError "invalid type"

leaf :: Parser Type_
leaf = do { defined DTType; return TType } <|>
       do { defined DO; return (Prod [O]) } <|>
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
      TType -> return ()
      Fun args res -> do { newFunction name (FunType args res); return () }
      Prod [res] -> do { newFunction name (FunType [] res); return () }
      _ -> fatalError "invalid type"
