-- Parse and typecheck TPTP clauses, stopping at include-clauses.

{-# LANGUAGE BangPatterns, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, TypeOperators, TypeFamilies, CPP, DeriveFunctor #-}
{-# OPTIONS_GHC -funfolding-use-threshold=1000 #-}
module Jukebox.TPTP.Parse.Core where

#include "errors.h"
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
import Jukebox.Utils
import Data.Symbol

import Jukebox.TPTP.Lexer hiding
  (Pos, Error, Include, Var, Type, Not, ForAll,
   Exists, And, Or, Type, Apply, Implies, Follows, Xor, Nand, Nor,
   Rational, Real, NegatedConjecture, Question,
   Axiom, Hypothesis, Definition, Assumption, Lemma, Theorem, NegatedConjecture,
   Conjecture, Question,
   keyword, defined, kind)
import qualified Jukebox.TPTP.Lexer as L
import qualified Jukebox.Form as Form
import Jukebox.Form hiding (tag, kind, newFunction, TypeOf(..), run)
import qualified Jukebox.Name as Name

-- The parser monad

data ParseState =
  MkState (Maybe String)           -- filename
          ![Input Form]            -- problem being constructed, inputs are in reverse order
          !(Map String Type)       -- types in scope
          !(Map String [Function]) -- functions in scope
          !(Map String Variable)   -- variables in scope, for CNF
          !Int64                   -- unique supply
type Parser = Parsec ParsecState
type ParsecState = UserState ParseState TokenStream

-- An include-clause.
data IncludeStatement = Include String (Maybe [Tag]) deriving Show

-- The initial parser state.
initialState :: Maybe String -> ParseState
initialState mfile =
  initialStateFrom mfile []
    (Map.fromList [(show (name ty), ty) | ty <- [intType, ratType, realType]])
    (Map.fromList
       [ (fun,
          [Fixed (Overloaded (intern fun) (intern (show (name kind)))) ::: ty
          | (kind, ty) <- tys ])
       | (fun, tys) <- funs ])
   where
     overloads f = [(ty, f ty) | ty <- [intType, ratType, realType]]
     fun xs f = [(x, overloads f) | x <- xs]

     funs =
       fun ["$less", "$lesseq", "$greater", "$greatereq"]
         (\ty -> FunType [ty, ty] O) ++
       fun ["$is_int", "$is_rat"]
         (\ty -> FunType [ty] O) ++
       fun ["$uminus", "$floor", "$ceiling", "$truncate", "$round"]
         (\ty -> FunType [ty] ty) ++
       fun ["$sum", "$difference", "$product",
            "$quotient_e", "$quotient_t", "$quotient_f",
            "$remainder_e", "$remainder_t", "$remainder_f"]
         (\ty -> FunType [ty, ty] ty) ++
       [("$quotient",
         [(ty, FunType [ty, ty] ty) | ty <- [ratType, realType]])] ++
       fun ["$to_int"]  (\ty -> FunType [ty] intType) ++
       fun ["$to_rat"]  (\ty -> FunType [ty] ratType) ++
       fun ["$to_real"] (\ty -> FunType [ty] realType)

initialStateFrom :: Maybe String -> [Name] -> Map String Type -> Map String [Function] -> ParseState
initialStateFrom mfile xs tys fs = MkState mfile [] tys fs Map.empty n
  where
    n = maximum (0:[succ m | Unique m _ _ <- xs])

instance Stream TokenStream Token where
  primToken (At _ (Cons Eof _)) _ok err _fatal = err
  primToken (At _ (Cons L.Error _)) _ok _err fatal = fatal "Lexical error"
  primToken (At _ (Cons t ts)) ok _err _fatal = ok ts t
  type Position TokenStream = TokenStream
  position = id

-- The main parsing function.
data ParseResult a =
    ParseFailed Location [String]
  | ParseSucceeded a
  | ParseStalled Location FilePath (String -> ParseResult a)
  deriving Functor

instance Applicative ParseResult where
  pure = return
  (<*>) = liftM2 ($)

instance Monad ParseResult where
  return = ParseSucceeded
  ParseFailed loc err >>= _ = ParseFailed loc err
  ParseSucceeded x >>= f = f x
  ParseStalled loc name k >>= f =
    ParseStalled loc name (\xs -> k xs >>= f)

data Location = Location FilePath Integer Integer
instance Show Location where
  show (Location file row col) =
    file ++ " (line " ++ show row ++ ", column " ++ show col ++ ")"

makeLocation :: FilePath -> L.Pos -> Location
makeLocation file (L.Pos row col) =
  Location file (fromIntegral row) (fromIntegral col)

parseProblem :: FilePath -> String -> ParseResult [Input Form]
parseProblem name contents = parseProblemFrom (initialState (Just name)) name contents

parseProblemFrom :: ParseState -> FilePath -> String -> ParseResult [Input Form]
parseProblemFrom state name contents =
  fmap finalise $
    aux Nothing name (UserState state (scan contents))
  where
    aux :: Maybe [Tag] -> FilePath -> ParsecState -> ParseResult ParseState
    aux tags name state =
      case run report (section (included tags)) state of
        (UserState{userStream = At pos _}, Left err) ->
          ParseFailed (makeLocation name pos) err
        (UserState{userState = state'}, Right Nothing) ->
          return state'
        (UserState state (input'@(At pos _)),
         Right (Just (Include name' tags'))) ->
          ParseStalled (makeLocation name pos) name' $ \input -> do
            state' <- aux (tags `merge` tags') name' (UserState state (scan input))
            aux tags name (UserState state' input')

    report :: ParsecState -> [String]
    report UserState{userStream = At _ (Cons Eof _)} =
      ["Unexpected end of file"]
    report UserState{userStream = At _ (Cons L.Error _)} =
      ["Lexical error"]
    report UserState{userStream = At _ (Cons t _)} =
      ["Unexpected " ++ show t]

    included :: Maybe [Tag] -> Tag -> Bool
    included Nothing _ = True
    included (Just xs) x = x `elem` xs

    merge :: Maybe [Tag] -> Maybe [Tag] -> Maybe [Tag]
    merge Nothing x = x
    merge x Nothing = x
    merge (Just xs) (Just ys) = Just (xs `intersect` ys)

    finalise :: ParseState -> Problem Form
    finalise (MkState _ p _ _ _ _) = check (reverse p)

-- Wee function for testing.
testParser :: Parser a -> String -> Either [String] a
testParser p s = snd (run (const []) p (UserState (initialState Nothing) (scan s)))

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
{-# INLINE ratNumber #-}
ratNumber = fmap ratValue (satisfy p)
  where p L.Rational{} = True
        p _ = False
{-# INLINE realNumber #-}
realNumber = fmap ratValue (satisfy p)
  where p L.Real{} = True
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
                 declaration Tff (\tag -> formulaIn tff tag <|> typeDeclaration) <|>
                 declaration Tcf (\tag -> formulaIn tff tag <|> typeDeclaration)
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
kind = do
  MkState mfile _ _ _ _ _ <- getState
  UserState _ (At (L.Pos n _) _) <- getPosition
  let
    general k kind = keyword k >> return (mk kind)
    axiom t kind = general t (Form.Ax kind)
    conjecture t kind = general t (Form.Conj kind)
    mk kind tag form =
      Input { Form.tag = tag,
              Form.kind = kind,
              Form.what = form,
              Form.source =
                case mfile of
                  Nothing -> Form.Unknown
                  Just file -> FromFile file (fromIntegral n) }
  axiom L.Axiom Axiom <|>
    axiom L.Hypothesis Hypothesis <|>
    axiom L.Definition Definition <|>
    axiom L.Assumption Assumption <|>
    axiom L.Lemma Lemma <|>
    axiom L.Theorem TheoremKind <|>
    axiom L.NegatedConjecture NegatedConjecture <|>
    conjecture L.Conjecture Conjecture <|>
    conjecture L.Question Question

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
  MkState mfile p t f v n <- getState
  putState (MkState mfile (input:p) t f v n)
  
newFunction :: String -> FunType -> Parser Function
newFunction name ty = do
  fs <- lookupFunction ty name
  case [ f | f <- fs, rhs f == ty ] of
    [] ->
      fatalError $ "Constant " ++ name ++
                   " was declared to have type " ++ prettyShow ty ++
                   " but already has type " ++ showTypes (map rhs fs)
    (f:_) -> return f

showTypes :: [FunType] -> String
showTypes = intercalate " and " . map prettyShow

{-# INLINE applyFunction #-}
applyFunction :: String -> [Term] -> Type -> Parser Term
applyFunction name args res = do
  fs <- lookupFunction (FunType (replicate (length args) indType) res) name
  case [ f | f <- fs, funArgs f == map typ args ] of
    [] -> typeError fs args
    (f:_) -> return (f :@: args)

{-# NOINLINE typeError #-}
typeError fs@(f@(x ::: _):_) args' = do
    let plural 1 x _ = x 
        plural _ _ y = y
        lengths = usort (map (length . funArgs) fs)
    fatalError $ "Type mismatch in term '" ++ prettyShow (prettyNames (f :@: args')) ++ "': " ++
                 "Constant " ++ prettyShow x ++
                 if length lengths == 1 && length args' `notElem` lengths then
                   " has arity " ++ show (head lengths) ++
                   " but was applied to " ++ show (length args') ++
                   plural (length args') " argument" " arguments"
                 else
                   " has type " ++ showTypes (map rhs fs) ++
                   " but was applied to " ++ plural (length args') "an argument" "arguments" ++
                   " of type " ++ intercalate ", " (map (prettyShow . typ) args')

{-# INLINE lookupType #-}
lookupType :: String -> Parser Type
lookupType xs = do
  MkState mfile p t f v n <- getState
  case Map.lookup xs t of
    Nothing -> do
      let ty = Type (name xs)
      putState (MkState mfile p (Map.insert xs ty t) f v n)
      return ty
    Just ty -> return ty

{-# INLINE lookupFunction #-}
lookupFunction :: FunType -> String -> Parser [Name ::: FunType]
lookupFunction def x = do
  MkState mfile p t f v n <- getState
  case Map.lookup x f of
    Nothing -> do
      let decl = name x ::: def
      putState (MkState mfile p t (Map.insert x [decl] f) v n)
      return [decl]
    Just fs -> return fs

-- Parsing formulae.

cnf, tff, fof :: Parser Form
cnf = do
  MkState mfile p t f _ n <- getState
  putState (MkState mfile p t f Map.empty n)
  form <- formula NoQuantification __
  return (closeForm form)
tff = formula Typed Map.empty
fof = formula Untyped Map.empty

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
  var :: Mode -> Map String Variable -> Parser a
  -- A parser for this type.
  parser :: Mode -> Map String Variable -> Parser a

data Mode = Typed | Untyped | NoQuantification

instance TermLike Form where
  {-# INLINE fromThing #-}
  fromThing (Apply x xs) = fmap (Literal . Pos . Tru) (applyFunction x xs O)
  fromThing (Term _) = mzero
  fromThing (Formula f) = return f
  -- A variable itself is not a valid formula.
  var _ _ = mzero
  parser = formula

instance TermLike Term where
  {-# INLINE fromThing #-}
  fromThing (Apply x xs) = applyFunction x xs indType
  fromThing (Term t) = return t
  fromThing (Formula _) = mzero
  parser = term

  {-# INLINE var #-}
  var NoQuantification _ = do
    x <- variable
    MkState mfile p t f ctx n <- getState
    case Map.lookup x ctx of
      Just v -> return (Var v)
      Nothing -> do
        let v = Unique (n+1) x defaultRenamer ::: indType
        putState (MkState mfile p t f (Map.insert x v ctx) (n+1))
        return (Var v)
  var _ ctx = do
    x <- variable
    case Map.lookup x ctx of
      Just v -> return (Var v)
      Nothing -> fatalError $ "unbound variable " ++ x

instance TermLike Thing where
  fromThing = return
  var mode ctx = fmap Term (var mode ctx)
  parser = formula

-- Types that can represent formulae. These are the types on which
-- you can use 'formula'.
class TermLike a => FormulaLike a where
  fromFormula :: Form -> a

instance FormulaLike Form where fromFormula = id
instance FormulaLike Thing where fromFormula = Formula

-- An atomic expression.
{-# INLINEABLE term #-}
term :: TermLike a => Mode -> Map String Variable -> Parser a
term mode ctx = function <|> var mode ctx <|> num <|> parens (parser mode ctx)
  where
    {-# INLINE function #-}
    function = do
      x <- atom
      args <- parens (sepBy1 (term mode ctx) (punct Comma)) <|> return []
      fromThing (Apply x args)

    {-# INLINE num #-}
    num = (int <|> rat <|> real)

    {-# INLINE int #-}
    int = do
      n <- number
      constant (Integer n) intType

    {-# INLINE rat #-}
    rat = do
      x <- ratNumber
      constant (Rational x) ratType

    {-# INLINE real #-}
    real = do
      x <- realNumber
      constant (Real x) realType

    {-# INLINE constant #-}
    constant x ty =
      fromThing (Term ((Fixed x ::: FunType [] ty) :@: []))

literal, unitary, quantified, formula ::
  FormulaLike a => Mode -> Map String Variable -> Parser a
{-# INLINE literal #-}
literal mode ctx = true <|> false <|> binary <?> "literal"
  where {-# INLINE true #-}
        true = do { defined DTrue; return (fromFormula (And [])) }
        {-# INLINE false #-}
        false = do { defined DFalse; return (fromFormula (Or [])) }
        binary = do
          x <- term mode ctx :: Parser Thing
          let {-# INLINE f #-}
              f p sign = do
               punct p
               lhs <- fromThing x :: Parser Term
               rhs <- term mode ctx :: Parser Term
               let form = Literal . sign $ lhs :=: rhs
               when (typ lhs /= typ rhs) $
                 fatalError $ "Type mismatch in equality '" ++ prettyShow (prettyNames form) ++
                              "': left hand side has type " ++ prettyShow (typ lhs) ++
                              " but right hand side has type " ++ prettyShow (typ rhs)
               when (typ lhs == O) $
                 fatalError $ "Type error in equality '" ++ prettyShow (prettyNames form) ++
                 "': can't use equality on predicate (use <=> or <~> instead)"
               return (fromFormula form)
          f Eq Pos <|> f Neq Neg <|> fromThing x

{-# INLINEABLE unitary #-}
unitary mode ctx = negation <|> quantified mode ctx <|> literal mode ctx
  where {-# INLINE negation #-}
        negation = do
          punct L.Not
          fmap (fromFormula . Not) (unitary mode ctx :: Parser Form)

{-# INLINE quantified #-}
quantified mode ctx = do
  q <- (punct L.ForAll >> return ForAll) <|>
       (punct L.Exists >> return Exists)
  vars <- bracks (sepBy1 (binder mode) (punct Comma))
  let ctx' = foldl' (\m v -> Map.insert (Name.base (Name.name v)) v m) ctx vars
  punct Colon
  rest <- unitary mode ctx' :: Parser Form
  return (fromFormula (q (Bind (Set.fromList vars) rest)))

-- A general formula.
{-# INLINEABLE formula #-}
formula mode ctx = do
  x <- unitary mode ctx :: Parser Thing
  let binop op t u = op [t, u]
      {-# INLINE connective #-}
      connective p op = do
        punct p
        lhs <- fromThing x
        rhs <- formula mode ctx :: Parser Form
        return (fromFormula (op lhs rhs))
  connective L.And (binop And) <|> connective L.Or (binop Or) <|>
   connective Iff Equiv <|>
   connective L.Implies (Connective Implies) <|>
   connective L.Follows (Connective Follows) <|>
   connective L.Xor (Connective Xor) <|>
   connective L.Nor (Connective Nor) <|>
   connective L.Nand (Connective Nand) <|>
   fromThing x

binder :: Mode -> Parser Variable
binder NoQuantification =
  fatalError "Used a quantifier in a CNF clause"
binder mode = do
  x <- variable
  ty <- do { punct Colon;
             case mode of {
               Typed -> return ();
               Untyped ->
                 fatalError "Used a typed quantification in an untyped formula" };
             type_ } <|> return indType
  MkState mfile p t f v n <- getState
  putState (MkState mfile p t f v (n+1))
  return (Unique n x defaultRenamer ::: ty)

-- Parse a type
type_ :: Parser Type
type_ =
  do { x <- atom; lookupType x } <|>
  do { defined DI; return indType }

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
