{-# LANGUAGE TypeSynonymInstances, MultiParamTypeClasses, ScopedTypeVariables, BangPatterns #-}
module Parser where

import Lexer hiding (Error, Type, Pos, Include, Var, keyword, defined)
import Formula hiding (kind, formula)
import qualified Lexer as L
import qualified Formula as F
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy as BSL
import Text.Parsec hiding (satisfy, anyToken, eof)
import Text.Parsec.Error
import Text.Parsec.Pos
import Text.Parsec.Prim
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Identity
import Control.Monad.Error
import Control.Exception hiding (try)
import qualified Data.Map as Map
import qualified Data.Set as Set
import ProgressBar
import FindFile
import Prelude hiding (catch)

parseProblem :: FilePath -> IO (Either ParseError (Problem Formula))
parseProblem name = withProgressBar $ \pb -> parseProblemWith (findFileTPTP []) pb name

-- The I/O part of the parser loop, which has the job of handling
-- include files, finding and reading files and updating the progress bar.
-- This is a bit icky.
instance Error ParseError where
  noMsg = strMsg "unknown error"
  strMsg msg = newErrorMessage (Message msg) (newPos "<unknown>" 0 0)

parseProblemWith :: (FilePath -> IO (Maybe FilePath)) -> ProgressBar -> FilePath -> IO (Either ParseError (Problem Formula))
parseProblemWith findFile progressBar name = runErrorT (fmap finalise (parseFile name Nothing pos0 p0))
  where p0 = Problem { types  = Map.fromList [(tname iType, iType)],
                       preds  = Map.empty,
                       funs   = Map.empty,
                       inputs = [] }
        pos0 = newPos "<command line>" 0 0
        iType = Type { tname = BS.pack "$i", tmonotone = Infinite, tsize = Infinite }

        err pos msg = throwError (newErrorMessage (Message msg) pos)
        liftMaybeIO :: IO (Maybe a) -> SourcePos -> String -> ErrorT ParseError IO a
        liftMaybeIO m pos msg = do
          x <- liftIO m
          case x of
            Nothing -> err pos msg
            Just x -> return x
        liftEitherIO :: IO (Either a b) -> SourcePos -> (a -> String) -> ErrorT ParseError IO b
        liftEitherIO m pos msg = do
          x <- liftIO m
          case x of
            Left e -> err pos (msg e)
            Right x -> return x

        problem :: ParseState -> Problem Formula
        problem (MkState prob _ _) = prob

        consume :: Consumed a -> a
        consume (Consumed x) = x
        consume (Empty x) = x

        parseFile :: FilePath -> Maybe [Token] -> SourcePos ->
                     Problem Formula -> ErrorT ParseError IO (Problem Formula)
        parseFile name clauses pos prob = do
          file <- liftMaybeIO (findFile name) pos ("File " ++ name ++ " not found")
          liftIO $ enter progressBar $ "Reading " ++ file
          contents <- liftEitherIO
                        (fmap Right (BSL.readFile file >>= tickOnRead progressBar)
                          `catch` (\(e :: IOException) -> return (Left e)))
                        (newPos file 0 0) show
          let At (L.Pos l c) tokens = scan contents
              pos' = newPos file (fromIntegral l) (fromIntegral c)
              s = State tokens pos' (MkState prob iType clauses)
          fmap (problem . stateUser) (parseSections s)

        parseSections :: State Contents ParseState ->
                         ErrorT ParseError IO (State Contents ParseState)
        parseSections s =
          case runIdentity (consume (runIdentity (runParsecT section s))) of
            Error e -> throwError e
            Ok Nothing s'@State{stateInput = Nil} _ -> do
              liftIO $ leave progressBar
              return s'
            Ok (Just (Include name clauses')) (State tokens pos (MkState prob i clauses)) _ -> do
              prob' <- parseFile (BS.unpack name) clauses' pos prob
              parseSections (State tokens pos (MkState prob' i clauses))

        finalise :: Problem Formula -> Problem Formula
        finalise p = p { inputs = reverse (inputs p) }

data IncludeStatement = Include BS.ByteString (Maybe [Token])

data ParseState =
  MkState !(Problem Formula) -- problem being constructed, inputs are in reverse order
          !Type              -- the $i type
          !(Maybe [Token])   -- only clauses with these names are added to the problem
type Parser = Parsec Contents ParseState

-- dummy instance---we have our own combinators for fetching from the
-- stream, since parsec struggles with our special Error token.
instance Stream Contents Identity Token where
  uncons = error "uncons: not implemented"

-- Primitive parsers.

satisfy p = mkPT $ \s ->
  let err msg = Identity (Empty (Identity (Error (newErrorMessage msg (statePos s))))) in
  case stateInput s of
    Nil -> err (UnExpect "end of input")
    Cons t (At (L.Pos l c) !ts) ->
      case p t of
        True ->
          let !pos' = flip setSourceLine (fromIntegral l) .
                      flip setSourceColumn (fromIntegral c) $ statePos s
              !s' = s { statePos = pos', stateInput = ts }
          in Identity (Consumed (Identity (Ok t s' (unknownError s'))))
        False -> err (UnExpect (show t))
    L.Error -> err (Message "lexical error")
eof = notFollowedBy (satisfy (const True)) <?> "end of input"

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
var = satisfy p <?> "variable"
  where p L.Var{} = True
        p _ = False
number = satisfy p <?> "number"
  where p Number{} = True
        p _ = False
atom = keyword' (const True) <?> "atom"
inputName = atom <|> number

-- Combinators.
parens, bracks :: Parser a -> Parser a
parens p = between (punct LParen) (punct RParen) p
bracks p = between (punct LBrack) (punct RBrack) p

binExpr :: Parser a -> Parser (a -> a -> Parser a) -> Parser a
binExpr leaf op = do
  lhs <- parens (binExpr leaf op) <|> leaf
  do { f <- op; rhs <- binExpr leaf op; f lhs rhs } <|> return lhs

-- Inserting types, predicates, functions and clauses.

newFormula :: Input Formula -> Parser ()
newFormula input = do
  MkState x i p <- getState
  let ok = case p of
             Nothing -> True
             Just names -> tag input `elem` names
  when ok $ setState $ MkState x{ inputs = input:inputs x } i p

findType :: BS.ByteString -> Parser Type
findType name = do
  MkState s i p <- getState
  case Map.lookup name (types s) of
    Nothing -> do
      let ty = Type { tname = name, tmonotone = Infinite, tsize = Infinite } 
      setState (MkState s{ types = Map.insert name ty (types s) } i p)
      return ty
    Just x -> return x

findPredicate :: BS.ByteString -> [Type] -> Parser Predicate
findPredicate name args = do
  MkState s i p <- getState
  case Map.lookup name (preds s) of
    Nothing -> do
      let pred = Predicate { pname = name }
      setState (MkState s{ preds = Map.insert name (args, pred) (preds s) } i p)
      return pred
    Just (args', _) | args /= args' ->
      fail $ "Expected " ++ BS.unpack name ++ " to have type " ++ showPredType args ++
             " but it has type " ++ showPredType args'
    Just (_, pred) ->
      return pred

findFunction :: BS.ByteString -> [Type] -> Type -> Parser Function
findFunction name args res = do
  MkState s i p <- getState
  case Map.lookup name (funs s) of
    Nothing -> do
      let fun = Function { fname = name, fres = res }
      setState (MkState s{ funs = Map.insert name (args, fun) (funs s) } i p)
      return fun
    Just (args', fun) | args /= args' || res /= fres fun ->
      fail $ "Expected " ++ BS.unpack name ++ " to have type " ++ showFunType args res ++
             " but it has type " ++ showFunType args' (fres fun)
    Just (_, fun) ->
      return fun

-- Parsing formulae.

input :: Parser ()
input = declaration Cnf (kinded cnf) <|>
        declaration Fof (kinded fof) <|>
        declaration Tff (\tag -> kinded tff tag <|> typeDeclaration)
  where declaration token p = do
          keyword token
          res <- parens $ do
            tag <- inputName
            punct Comma
            p tag
          punct Dot
          return res
        kinded p tag = do
          k <- kind
          punct Comma
          res <- p
          newFormula (k tag res)
        kind = axiom L.Axiom <|> 
               axiom L.Hypothesis <|>
               axiom L.Definition <|>
               axiom L.Assumption <|>
               axiom L.Lemma <|>
               axiom L.Theorem <|>
               conjecture L.Conjecture <|>
               conjecture L.Question <|>
               do { keyword L.NegatedConjecture; return (form id F.NegatedConjecture) }
        axiom k = do { keyword k; return (form id F.Axiom) }
        conjecture k = do { keyword k; return (form nt F.NegatedConjecture) }
        form f kind tag formula = Input { tag = tag, F.kind = kind, F.formula = f formula }

-- Parse an include line
include :: Parser IncludeStatement
include = do
  keyword L.Include
  res <- parens $ do
    Atom{name = name} <- atom
    clauses <- do { punct Comma
                  ; fmap Just (bracks (sepBy inputName (punct Comma))) } <|> return Nothing
    return (Include name clauses)
  punct Dot
  return res

-- Parse until an include line
section :: Parser (Maybe IncludeStatement)
section = many input >> (fmap Just include <|> (eof >> return Nothing))

-- Parse a TFF type declaration

data TypeAST = TypeAST | BooleanAST | ProdAST [Type]
productType :: TypeAST -> TypeAST -> Parser TypeAST
productType (ProdAST tys) (ProdAST tys2) = return $ ProdAST (tys ++ tys2)
productType _ _ = fail "invalid type"
leafType :: Parser TypeAST
leafType = do { defined DTType; return TypeAST } <|>
           do { defined DO; return BooleanAST } <|>
           do { ty <- type_; return (ProdAST [ty]) }

typeDeclaration :: Parser ()
typeDeclaration = do
  keyword L.Type
  punct Comma
  let manyParens p = parens (manyParens p) <|> p
  manyParens $ do
    Atom { name = name } <- atom
    punct Colon
    lhs <- binExpr leafType (punct Times >> return productType)
    rhs <- optionMaybe (punct FunArrow >> leafType)
    case (lhs, rhs) of
      (TypeAST, Nothing) -> do { findType name; return () }
      (BooleanAST, Nothing) -> do { findPredicate name []; return () }
      (ProdAST [res], Nothing) -> do { findFunction name [] res; return () }
      (ProdAST args, Just BooleanAST) -> do { findPredicate name args; return () }
      (ProdAST args, Just (ProdAST [res])) -> do { findFunction name args res; return () }
      _ -> fail "invalid type"
 
tff, fof, cnf :: Parser Formula
tff = formula (varDecl True)
fof = formula (varDecl False)
cnf = fail "cnf not supported yet"

formula :: Parser Variable -> Parser Formula
formula = undefined

-- varDecl True: parse a typed variable binding X:a or an untyped one X
-- varDecl Fals: parse an untyped variable binding X
varDecl :: Bool -> Parser Variable
varDecl typed = do
  x <- var
  ty <- do { punct Colon;
             when (not typed) $
               fail "Used a typed quantification in an untyped formula";
             type_ } <|> individual
  return Variable { vname = name x, vtype = ty }

-- Parse a type
type_ :: Parser Type
type_ =
  do { Atom { name = name } <- atom; findType name } <|>
  do { defined DI; individual }

-- The type $i (anything whose type is not specified gets this type)
individual :: Parser Type
individual = do
  MkState _ i _ <- getState
  return i
