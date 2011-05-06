{-# LANGUAGE TypeSynonymInstances, MultiParamTypeClasses, ScopedTypeVariables #-}
module Parser where

import Lexer hiding (Error, Type, Pos, Include, Var, keyword, defined)
import Formula hiding (kind, formula)
import qualified Lexer as L
import qualified Formula as F
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy as BSL
import Parsimony hiding (Parser)
import Parsimony.Error
import Parsimony.Pos
import Parsimony.Stream hiding (Token)
import qualified Parsimony.Stream
import Parsimony.UserState
import Control.Monad
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
parseProblemWith :: (FilePath -> IO (Maybe FilePath)) -> ProgressBar -> FilePath -> IO (Either ParseError (Problem Formula))
parseProblemWith findFile progressBar name = do
  let s0 = MkState p0 iType Nothing
      p0 = Problem { types  = Map.fromList [(tname iType, iType)],
                     preds  = Map.empty,
                     funs   = Map.empty,
                     inputs = [] }
      iType = Type { tname = BS.pack "$i", tmonotone = Infinite, tsize = Infinite }
      -- read and parse a new file
      push name clauses ss s pos = do
        let err msg = return (Left (newErrorMessage (Message msg) pos))
        file <- findFile name
        case file of
          Nothing -> err $ "File " ++ name ++ " not found"
          Just file -> do
            contents <- fmap Right (BSL.readFile file) `catch`
                        (\(e :: IOException) -> return (Left e))
            case contents of
              Left e ->
                err $ "Couldn't read file " ++ file
              Right contents ->
                let At (L.Pos l c) tokens = scan contents
                    pos = newPos file (fromIntegral l) (fromIntegral c)
                    s' = State (UserState (pushState clauses s) tokens) pos
                in go s' ss
      -- continue parsing
      go s ss =
        case runParser section s of
          Error e -> return (Left e)
          Ok Nothing s' ->
            goEof s' ss
          Ok (Just (Include name clauses)) s' ->
            push (BS.unpack name) clauses (s':ss) (userState (stateInput s')) (statePos s')
      -- decide what to do at end-of-file/lexical-error
      goEof s ss =
        case parserStream (stateInput s) of
          Nil -> resume (userState (stateInput s)) ss
          L.Error ->
            let msg = "Lexical error"
                pos = statePos s
            in return (Left (newErrorMessage (Message msg) pos))
          _ -> error "Parser.parseProblemWith.goEof: not at end of file"
      resume s [] =
        return (Right (extractProblem s))
      resume s' (s:ss) =
        go (popState s' s) ss

      extractProblem (MkState p _ _) = p { inputs = reverse (inputs p) }
      pushState clauses (MkState p i _) = MkState p i clauses
      popState (MkState p _ _) (State (UserState (MkState _ i cs) tokens) pos) = State (UserState (MkState p i cs) tokens) pos
                
  push name Nothing [] s0 (newPos "<command line>" 0 0)

data IncludeStatement = Include BS.ByteString (Maybe [Token])

data ParseState =
  MkState !(Problem Formula) -- problem being constructed, inputs are in reverse order
          !Type              -- the $i type
          !(Maybe [Token])   -- only clauses with these names are added to the problem
type Parser = ParserU ParseState Contents

-- Interfacing with Alex: how to get a token from a token stream
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
  MkState x i p <- getUserState
  let ok = case p of
             Nothing -> True
             Just names -> tag input `elem` names
  when ok $ setUserState $ MkState x{ inputs = input:inputs x } i p

findType :: BS.ByteString -> Parser Type
findType name = do
  MkState s i p <- getUserState
  case Map.lookup name (types s) of
    Nothing -> do
      let ty = Type { tname = name, tmonotone = Infinite, tsize = Infinite } 
      setUserState (MkState s{ types = Map.insert name ty (types s) } i p)
      return ty
    Just x -> return x

findPredicate :: BS.ByteString -> [Type] -> Parser Predicate
findPredicate name args = do
  MkState s i p <- getUserState
  case Map.lookup name (preds s) of
    Nothing -> do
      let pred = Predicate { pname = name }
      setUserState (MkState s{ preds = Map.insert name (args, pred) (preds s) } i p)
      return pred
    Just (args', _) | args /= args' ->
      fail $ "Expected " ++ BS.unpack name ++ " to have type " ++ showPredType args ++
             " but it has type " ++ showPredType args'
    Just (_, pred) ->
      return pred

findFunction :: BS.ByteString -> [Type] -> Type -> Parser Function
findFunction name args res = do
  MkState s i p <- getUserState
  case Map.lookup name (funs s) of
    Nothing -> do
      let fun = Function { fname = name, fres = res }
      setUserState (MkState s{ funs = Map.insert name (args, fun) (funs s) } i p)
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
    rhs <- optional (punct FunArrow >> leafType)
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
  MkState _ i _ <- getUserState
  return i
