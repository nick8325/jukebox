-- Parse and typecheck TPTP clauses, stopping at include-clauses.

{-# LANGUAGE BangPatterns, MultiParamTypeClasses, ImplicitParams, FlexibleInstances, TypeOperators, TypeFamilies #-}
module TPTP.ClauseParser where

import TPTP.Parsec
import Control.Applicative
import Control.Monad
import qualified Data.ByteString.Lazy.Char8 as BSL
import qualified Data.ByteString.Char8 as BS
import qualified Map
import Map(Map)
import qualified Seq as S
import Seq(Seq)
import Data.List
import TPTP.Print
import Name hiding (name)
import qualified NameMap

import TPTP.Lexer hiding
  (Pos, Error, Include, Var, Type, Not, ForAll,
   Exists, And, Or, Type, Apply, Implies, Follows, Xor, Nand, Nor,
   keyword, defined, kind)
import qualified TPTP.Lexer as L
import qualified Form
import Form hiding (tag, kind, Axiom, Conjecture, Question)
import qualified Name

-- The parser monad

data ParseState =
  MkState ![Input Form]                           -- problem being constructed, inputs are in reverse order
          !(Map BS.ByteString Type)               -- types
          !(Map BS.ByteString (Name ::: FunType)) -- functions
          !(Map BS.ByteString (Name ::: Type))    -- free variables in CNF clause
          !Type                                   -- the $i type
          !Int                                    -- the next type equivalence class
          !(Closed ())                            -- name generation
type Parser = Parsec ParsecState
type ParsecState = UserState ParseState TokenStream

-- An include-clause.
data IncludeStatement = Include BS.ByteString (Maybe [Tag]) deriving Show

-- The initial parser state.
initialState :: ParseState
initialState = MkState [] (Map.insert (BS.pack "$i") typeI Map.empty) Map.empty Map.empty typeI 1 closed0
  where typeI = Type nameI Infinite Infinite 0

instance Stream TokenStream Token where
  primToken (At _ (Cons Eof _)) ok err fatal = err
  primToken (At _ (Cons L.Error _)) ok err fatal = fatal "Lexical error"
  primToken (At _ (Cons t ts)) ok err fatal = ok ts t
  type Position TokenStream = TokenStream
  position = id

-- Wee function for testing.
testParser :: Parser a -> String -> Either [String] a
testParser p s = snd (run (const []) p (UserState initialState (scan (BSL.pack s))))

getProblem :: Parser [Input Form]
getProblem = do
  MkState p _ _ _ _ _ _ <- getState
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
variable = fmap name (satisfy p) <?> "variable"
  where p L.Var{} = True
        p _ = False
{-# INLINE number #-}
number = fmap value (satisfy p) <?> "number"
  where p Number{} = True
        p _ = False
{-# INLINE atom #-}
atom = fmap name (keyword' (const True)) <?> "atom"

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

-- Inserting types, functions and clauses.

newFormula :: Input Form -> Parser ()
newFormula input = do
  MkState p t f v i c n <- getState
  putState (MkState (input:p) t f Map.empty i c n)
  
newNameFrom :: Named a => Closed () -> a -> (Closed (), Name)
newNameFrom n name = (close_ n' (return ()), open n')
  where n' = close_ n (newName name)

{-# INLINE findType #-}
findType :: BS.ByteString -> Parser Type
findType name = do
  MkState p t f v i c n <- getState
  case Map.lookup name t of
    Nothing -> do
      let (n', name') = newNameFrom n name
          ty = Type { tname = name', tmonotone = Infinite, tsize = Infinite, tclass = c }
      putState (MkState p (Map.insert name ty t) f v i (c+1) n')
      return ty
    Just x -> return x

newFunction :: BS.ByteString -> FunType -> Parser (Name ::: FunType)
newFunction name ty' = do
  f@(_ ::: ty) <- lookupFunction ty' name
  unless (ty == ty') $ do
    fatalError $ "Constant " ++ BS.unpack name ++
                 " was declared to have type " ++ prettyShow ty' ++
                 " but already has type " ++ prettyShow ty
  return f

{-# INLINE applyFunction #-}
applyFunction :: BS.ByteString -> [Term] -> Type -> Parser Term
applyFunction name args' res = do
  i <- individual
  f@(_ ::: ty) <- lookupFunction (FunType (replicate (length args') i) res) name
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
                   plural (length (args ty)) "argument" "arguments"

{-# INLINE lookupFunction #-}
lookupFunction :: FunType -> BS.ByteString -> Parser (Name ::: FunType)
lookupFunction def name = do
  MkState p t f v i c n <- getState
  case Map.lookup name f of
    Nothing -> do
      let (n', name') = newNameFrom n name
          decl = name' ::: def
      putState (MkState p t (Map.insert name decl f) v i c n')
      return decl
    Just f -> return f

-- The type $i (anything whose type is not specified gets this type)
{-# INLINE individual #-}
individual :: Parser Type
individual = do
  MkState _ _ _ _ i _ _ <- getState
  return i

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
data Thing = Apply !BS.ByteString ![Term]
           | Term !Term
           | Formula !Form

instance Show Thing where
  show (Apply f []) = BS.unpack f
  show (Apply f args) =
    BS.unpack f ++
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
  var :: (?ctx :: Maybe (Map BS.ByteString Variable)) => Parser a
  -- A parser for this type.
  parser :: (?binder :: Parser Variable,
             ?ctx :: Maybe (Map BS.ByteString Variable)) => Parser a

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
  fromThing t@(Apply x xs) = individual >>= applyFunction x xs
  fromThing (Term t) = return t
  fromThing (Formula _) = mzero
  parser = term
  var = do
    x <- variable
    case ?ctx of
      Nothing -> do
        MkState p t f vs i c n <- getState
        case Map.lookup x vs of
          Just v -> return (Var v)
          Nothing -> do
            let (n', name) = newNameFrom n x
                v = name ::: i
            putState (MkState p t f (Map.insert x v vs) i c n')
            return (Var v)
      Just ctx ->
        case Map.lookup x ctx of
          Just v -> return (Var v)
          Nothing -> fatalError $ "unbound variable " ++ BS.unpack x

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
{-# SPECIALISE term :: (?binder :: Parser Variable, ?ctx :: Maybe (Map BS.ByteString Variable)) => Parser Term #-}
{-# SPECIALISE term :: (?binder :: Parser Variable, ?ctx :: Maybe (Map BS.ByteString Variable)) => Parser Form #-}
{-# SPECIALISE term :: (?binder :: Parser Variable, ?ctx :: Maybe (Map BS.ByteString Variable)) => Parser Thing #-}
term :: (?binder :: Parser Variable, ?ctx :: Maybe (Map BS.ByteString Variable), TermLike a) => Parser a
term = function <|> var <|> parens parser
  where {-# INLINE function #-}
        function = do
          x <- atom
          args <- parens (sepBy1 term (punct Comma)) <|> return []
          fromThing (Apply x args)

literal, unitary, quantified, formula ::
  (?binder :: Parser Variable, ?ctx :: Maybe (Map BS.ByteString Variable), FormulaLike a) => Parser a
{-# INLINE literal #-}
literal = true <|> false <|> binary <?> "literal"
  where {-# INLINE true #-}
        true = do { defined DTrue; return (fromFormula (And S.Nil)) }
        {-# INLINE false #-}
        false = do { defined DFalse; return (fromFormula (Or S.Nil)) }
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

{-# SPECIALISE unitary :: (?binder :: Parser Variable, ?ctx :: Maybe (Map BS.ByteString Variable)) => Parser Form #-}
{-# SPECIALISE unitary :: (?binder :: Parser Variable, ?ctx :: Maybe (Map BS.ByteString Variable)) => Parser Thing #-}
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
  return (fromFormula (q (Bind (NameMap.fromList vars) rest)))

-- A general formula.
{-# SPECIALISE formula :: (?binder :: Parser Variable, ?ctx :: Maybe (Map BS.ByteString Variable)) => Parser Form #-}
{-# SPECIALISE formula :: (?binder :: Parser Variable, ?ctx :: Maybe (Map BS.ByteString Variable)) => Parser Thing #-}
formula = do
  x <- unitary :: Parser Thing
  let binop op t u = op (S.Unit t `S.append` S.Unit u)
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
             type_ } <|> individual
  MkState p t f v i c n <- getState
  let (n', name) = newNameFrom n x
  putState (MkState p t f v i c n')
  return (name ::: ty)

-- Parse a type
type_ :: Parser Type
type_ =
  do { name <- atom; findType name } <|>
  do { defined DI; individual }

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
      TType -> do { findType name; return () }
      Fun args res -> do { newFunction name (FunType args res); return () }
      Prod [res] -> do { newFunction name (FunType [] res); return () }
      _ -> fatalError "invalid type"
