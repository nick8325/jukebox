-- Parse and typecheck TPTP clauses, stopping at include-clauses.

{-# LANGUAGE BangPatterns, MultiParamTypeClasses, ImplicitParams, FlexibleInstances #-}
module TPTP.ClauseParser where

import TPTP.Parsec
import Control.Applicative
import Control.Monad
import qualified Data.ByteString.Lazy.Char8 as BSL
import qualified Data.ByteString.Char8 as BS
import qualified Data.HashMap as Map
import Data.HashMap(Map)
import qualified Data.Set as Set
import qualified AppList
import AppList(AppList)
import Data.List
import TPTP.Print
import Text.PrettyPrint.HughesPJClass hiding (parens)

import TPTP.Lexer hiding
  (Pos, Error, Include, Var, Type, Not, ForAll,
   Exists, And, Or, Type, Apply, keyword, defined, kind)
import qualified TPTP.Lexer as L
import qualified Formula
import Formula hiding (tag, kind, formula, Axiom, NegatedConjecture)

-- The parser monad

data ParseState =
  MkState !(Problem Formula Name) -- problem being constructed, inputs are in reverse order
          !(Maybe (Type Name))    -- the $i type, if used in the problem
  deriving Show
type Parser = Parsec ParsecState
type ParsecState = UserState ParseState TokenStream

-- An include-clause.
data IncludeStatement = Include BS.ByteString (Maybe [Tag]) deriving Show

-- The initial parser state.
initialState :: ParseState
initialState = MkState (Problem Map.empty Map.empty Map.empty [] []) Nothing

instance Stream TokenStream Token where
  primToken (At _ Nil) ok err fatal = err
  primToken (At _ L.Error) ok err fatal = fatal "Lexical error"
  primToken (At _ (Cons t ts)) ok err fatal = ok ts t

-- Wee function for testing.
testParser :: Parser a -> String -> Either [String] a
testParser p s = snd (run (const []) p (UserState initialState (scan (BSL.pack s))))

getProblem :: Parser (Problem Formula Name)
getProblem = do
  MkState p _ <- getState
  return p { inputs = reverse (inputs p) }

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
kind :: Parser (Tag -> Formula Name -> Input (Formula Name))
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

newFormula :: Input (Formula Name) -> Parser ()
newFormula input = do
  MkState p i <- getState
  putState (MkState p{ inputs = input:inputs p } i)

{-# INLINE findType #-}
findType :: BS.ByteString -> Parser (Type Name)
findType name = do
  MkState p i <- getState
  case Map.lookup name (types p) of
    Nothing -> do
      let ty = Type { tname = name, tmonotone = Infinite, tsize = Infinite } 
      putState (MkState p{ types = Map.insert name ty (types p) } i)
      return ty
    Just x -> return x

newFunction :: BS.ByteString -> [Type Name] -> Type Name -> Parser (Function Name)
newFunction name args res =
  new "Function" (lookupFunction f) check decl showSym name args
    where check f = res == fres f
          decl = showFunType args res
          showSym args' f = showFunType args' (fres f)
          f = return (args, Function { fname = name, fres = res })

newPredicate :: BS.ByteString -> [Type Name] -> Parser (Predicate Name)
newPredicate name args =
  new "Predicate" (lookupPredicate p) (const True) decl showSym name args
    where decl = showPredType args
          showSym args' _ = showPredType args'
          p = return (args, Predicate { pname = name })

new kind lookup check decl showSym name args = do
  (args', f) <- lookup name
  unless (args == args' && check f) $ do
    fatalError $ kind ++ " " ++ BS.unpack name ++
                 " was declared to have type " ++ decl ++
                 " but already has type " ++ showSym args' f
  return f

{-# INLINE applyFunction #-}
applyFunction :: BS.ByteString -> [Term Name] -> Parser (Term Name)
applyFunction name args = lookupFunction f name >>= typeCheck "Function" ty (:@:) args
  where ty args f = showFunType args (fres f)
        f = do tys <- mapM (const individual) args
               res <- individual
               return (tys, Function { fname = name, fres = res })

{-# INLINE applyPredicate #-}
applyPredicate :: BS.ByteString -> [Term Name] -> Parser (Atom Name)
applyPredicate name args = lookupPredicate p name >>= typeCheck "Predicate" ty (:?:) args
  where ty args _ = showPredType args
        p = do tys <- mapM (const individual) args
               return (tys, Predicate { pname = name })

{-# INLINE typeCheck #-}
typeCheck kind showTy app args (args', fun) = do
  unless (map ty args == args') $ typeError kind showTy app args args' fun
  return (fun `app` args)

{-# NOINLINE typeError #-}
typeError kind showTy app args args' fun = do
    let plural 1 x y = x 
        plural _ x y = y
    fatalError $ "Type mismatch in term '" ++ prettyShow (fun `app` args) ++ "': " ++
                 kind ++ " " ++ prettyShow fun ++
                 if length args == length args' then
                   " has type " ++ showTy args' fun ++
                   " but was applied to " ++ plural (length args) "an argument" "arguments" ++
                   " of type " ++ showArgs (map ty args)
                 else
                   " has arity " ++ show (length args') ++
                   " but was applied to " ++ show (length args) ++
                   plural (length args) "argument" "arguments"

{-# INLINE lookupFunction #-}
lookupFunction :: Parser ([Type Name], Function Name) -> BS.ByteString -> Parser ([Type Name], Function Name)
lookupFunction = look funs (\p x -> p { funs = x })

{-# INLINE lookupPredicate #-}
lookupPredicate :: Parser ([Type Name], Predicate Name) -> BS.ByteString -> Parser ([Type Name], Predicate Name)
lookupPredicate = look preds (\p x -> p { preds = x })

{-# INLINE look #-}
look get put def name = do
  MkState p i <- getState
  case Map.lookup name (get p) of
    Nothing -> do
      f <- def
      putState (MkState (put p (Map.insert name f (get p))) i)
      return f
    Just f -> return f

-- The type $i (anything whose type is not specified gets this type)
{-# INLINE individual #-}
individual :: Parser (Type Name)
individual = do
  MkState p i <- getState
  case i of
    Nothing -> do
      ind <- findType (BS.pack "$i")
      putState (MkState p (Just ind))
      return ind
    Just x -> return x

-- Parsing formulae.

cnf, tff, fof :: Parser (Formula Name)
cnf = fatalError "cnf not implemented"
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
data Thing = Apply !BS.ByteString ![Term Name]
           | Term !(Term Name)
           | Formula !(Formula Name)

instance Pretty Thing where
  pPrintPrec l _ (Apply f xs) = prettyFunc l (pPrint f) xs
  pPrintPrec l p (Term t) = pPrintPrec l p t
  pPrintPrec l p (Formula f) = pPrintPrec l p f

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
  {-# INLINE fromThing #-}
  fromThing :: Thing -> Parser a
  -- Parse a variable occurrence as a term on its own, if that's allowed.
  {-# INLINE var #-}
  var :: (?ctx :: Map BS.ByteString (Variable Name)) => Parser a
  -- A parser for this type.
  parser :: (?binder :: Parser (Variable Name),
             ?ctx :: Map BS.ByteString (Variable Name)) => Parser a

instance TermLike (Formula Name) where
  fromThing t@(Apply x xs) = fmap (Literal . Pos) (applyPredicate x xs)
  fromThing (Term _) = mzero
  fromThing (Formula f) = return f
  -- A variable itself is not a valid formula.
  var = mzero
  parser = formula

instance TermLike (Term Name) where
  fromThing t@(Apply x xs) = applyFunction x xs
  fromThing (Term t) = return t
  fromThing (Formula _) = mzero
  parser = term
  var = do
    x <- variable
    case Map.lookup x ?ctx of
      Just v -> return (Var v)
      Nothing -> fatalError $ "unbound variable " ++ BS.unpack x

instance TermLike Thing where
  fromThing = return
  var = fmap Term var
  parser = formula

-- Types that can represent formulae. These are the types on which
-- you can use 'formula'.
class TermLike a => FormulaLike a where
  {-# INLINE fromFormula #-}
  fromFormula :: Formula Name -> a
instance FormulaLike (Formula Name) where fromFormula = id
instance FormulaLike Thing where fromFormula = Formula

-- An atomic expression.
{-# SPECIALISE term :: (?binder :: Parser (Variable Name), ?ctx :: Map BS.ByteString (Variable Name)) => Parser (Term Name) #-}
{-# SPECIALISE term :: (?binder :: Parser (Variable Name), ?ctx :: Map BS.ByteString (Variable Name)) => Parser (Formula Name) #-}
{-# SPECIALISE term :: (?binder :: Parser (Variable Name), ?ctx :: Map BS.ByteString (Variable Name)) => Parser Thing #-}
term :: (?binder :: Parser (Variable Name), ?ctx :: Map BS.ByteString (Variable Name), TermLike a) => Parser a
term = function <|> var <|> parens parser
  where {-# INLINE function #-}
        function = do
          x <- atom
          args <- parens (sepBy1 term (punct Comma)) <|> return []
          fromThing (Apply x args)

literal, unitary, quantified, formula ::
  (?binder :: Parser (Variable Name), ?ctx :: Map BS.ByteString (Variable Name), FormulaLike a) => Parser a
{-# INLINE literal #-}
literal = true <|> false <|> binary <?> "literal"
  where {-# INLINE true #-}
        true = do { defined DTrue; return (fromFormula (And AppList.Nil)) }
        {-# INLINE false #-}
        false = do { defined DFalse; return (fromFormula (Or AppList.Nil)) }
        binary = do
          x <- term :: Parser Thing
          let {-# INLINE f #-}
              f p sign = do
               punct p
               lhs <- fromThing x :: Parser (Term Name)
               rhs <- term :: Parser (Term Name)
               let form = Literal . sign $ lhs :=: rhs
               when (ty lhs /= ty rhs) $
                 fatalError $ "Type mismatch in equality '" ++ prettyShow form ++ 
                              "': left hand side has type " ++ prettyShow (ty lhs) ++
                              " but right hand side has type " ++ prettyShow (ty rhs)
               return (fromFormula form)
          f Eq Pos <|> f Neq Neg <|> fromThing x

{-# SPECIALISE unitary :: (?binder :: Parser (Variable Name), ?ctx :: Map BS.ByteString (Variable Name)) => Parser (Formula Name) #-}
{-# SPECIALISE unitary :: (?binder :: Parser (Variable Name), ?ctx :: Map BS.ByteString (Variable Name)) => Parser Thing #-}
unitary = negation <|> quantified <|> literal
  where {-# INLINE negation #-}
        negation = do
          punct L.Not
          fmap (fromFormula . Not) (unitary :: Parser (Formula Name))

{-# INLINE quantified #-}
quantified = do
  q <- (punct L.ForAll >> return ForAll) <|>
       (punct L.Exists >> return Exists)
  vars <- bracks (sepBy1 ?binder (punct Comma))
  let ctx' = foldl' (\m v -> Map.insert (vname v) v m) ?ctx vars
  punct Colon
  rest <- let ?ctx = ctx' in (unitary :: Parser (Formula Name))
  return (fromFormula (q (Set.fromList vars) rest))

-- A general formula.
{-# SPECIALISE formula :: (?binder :: Parser (Variable Name), ?ctx :: Map BS.ByteString (Variable Name)) => Parser (Formula Name) #-}
{-# SPECIALISE formula :: (?binder :: Parser (Variable Name), ?ctx :: Map BS.ByteString (Variable Name)) => Parser Thing #-}
formula = do
  x <- unitary :: Parser Thing
  let binop op t u = op (AppList.Unit t `AppList.append` AppList.Unit u)
      {-# INLINE connective #-}
      connective p op = do
        punct p
        lhs <- fromThing x
        rhs <- formula :: Parser (Formula Name)
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
-- varDecl False: parse an untyped variable binding X
varDecl :: Bool -> Parser (Variable Name)
varDecl typed = do
  x <- variable
  ty <- do { punct Colon;
             when (not typed) $
               fatalError "Used a typed quantification in an untyped formula";
             type_ } <|> individual
  return Variable { vname = x, vtype = ty }

-- Parse a type
type_ :: Parser (Type Name)
type_ =
  do { name <- atom; findType name } <|>
  do { defined DI; individual }

-- A little data type to help with parsing types.
data Type_ = TType | O | Fun [Type Name] (Type Name)
           | Pred [Type Name] | Prod [Type Name]

prod :: Type_ -> Type_ -> Parser Type_
prod (Prod tys) (Prod tys2) = return $ Prod (tys ++ tys2)
prod _ _ = fatalError "invalid type"

arrow :: Type_ -> Type_ -> Parser Type_
arrow (Prod ts) (Prod [x]) = return $ Fun ts x
arrow (Prod ts) O = return $ Pred ts
arrow _ _ = fatalError "invalid type"

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
      O -> do { newPredicate name []; return () }
      Fun args res -> do { newFunction name args res; return () }
      Pred args -> do { newPredicate name args; return () }
      Prod [res] -> do { newFunction name [] res; return () }
      _ -> fatalError "invalid type"
