{-# LANGUAGE TypeSynonymInstances, MultiParamTypeClasses #-}
module Parser where

import qualified Lexer as L
import Formula
import Progress
import TPTP
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL
import Text.Parsec hiding (Empty, Error, anyToken, token, satisfy)
import Text.Parsec.Error
import Text.Parsec.Pos
import qualified Control.Monad.Trans.Error as E
import Control.Monad.Trans.Class
import Control.Monad

data Pos = MkPos FilePath {-# UNPACK #-} !L.Pos
data InputState = At {-# UNPACK #-} !Pos !Contents
data Contents = Empty | Error | Token !L.Token !L.TokenStream [(FilePath, L.TokenStream)]

type M = E.ErrorT Pos (Progress (TPTP IO)) -- ErrorT Pos is for reporting lex errors
type Parser = ParsecT InputState Int M

instance E.Error Pos where
  noMsg = error "instance Error Pos: not implemented"
  strMsg = error "instance Error Pos: not implemented"

instance Stream InputState M L.Token where
  uncons (At _ Empty) = return Nothing
  uncons (At pos Error) = E.throwError pos
  uncons (At (MkPos file _) (Token t ts xs)) = return (Just (t, nextState file ts xs))

{-# INLINE nextState #-}
nextState :: FilePath -> L.TokenStream -> [(FilePath, L.TokenStream)] -> InputState
nextState file (L.At pos L.Nil) xs = nextFile (MkPos file pos) xs
nextState file (L.At pos (L.Cons t ts)) xs = At (MkPos file pos) (Token t ts xs)
nextState file (L.At pos L.Error) _ = At (MkPos file pos) Error

{-# NOINLINE nextFile #-}
nextFile :: Pos -> [(FilePath, L.TokenStream)] -> InputState
nextFile pos [] = At pos Empty
nextFile _ ((file, ts):xs) = nextState file ts xs

token :: (L.Token -> Maybe a) -> Parser a
token f = lift (lift tick) >> tokenPrim show (\_ _ (At pos _) -> sourcePos pos) f

anyToken = token Just
satisfy p = token (\x -> if p x then Just x else Nothing)

sourcePos (MkPos file (L.Pos l c)) = newPos file (fromIntegral l) (fromIntegral c)

countTokens :: Parser Int
countTokens = skipMany (satisfy isAtom >> satisfy (isPunct L.LParen) >> brackets >> satisfy (isPunct L.RParen) >> satisfy (isPunct L.Dot)) >> eof >> getState
  where isPunct k L.Punct{L.kind=k'} = k == k'
        isPunct k _ = False
        isAtom L.Atom{L.keyword=L.Axiom} = True
        isAtom _ = False
        brackets = (satisfy (isPunct L.LParen) >> modifyState (+1) >> skipMany brackets >> satisfy (isPunct L.RParen)) <|>
                   (satisfy (not . isPunct L.RParen))

runParser :: Parser a -> FilePath -> L.TokenStream -> IO (Either ParseError a)
runParser p file ts = do
  let state@(At pos _) = nextState file ts []
      errorT = runParserT (setPosition (sourcePos pos) >> p) 0 file state
      progress = E.runErrorT errorT
      tptp = runProgress progress 100000 $ "Parsing " ++ file ++ ".."
      io = runTPTP tptp (const (return Nothing))
  res <- io
  case res of
    Left pos ->
      return (Left (newErrorMessage (Message "lexical error") (sourcePos pos)))
    Right x ->
      return x

-- -- Ye gods, this is HORRIBLE!
-- token :: (L.Token -> Maybe a) -> Parser a
-- token f = do
--   r <- tokenPrim show (\_ _ 

-- -- foo :: FilePath -> StateT ParseState (Progress (TPTP IO)) BSL.ByteString
-- -- foo name = do
-- --   t <- gets tokens
-- --   if t == 250000 then do
-- --     modify (\s -> s { tokens = 0 })
-- --     lift tick
-- --     return BSL.empty
-- --    else do
-- --     x <- lift (lift (readTPTPFile name))
-- --     case x of
-- --       Nothing -> return BSL.empty
-- --       Just x -> return x

-- foo :: FilePath -> Progress (TPTP IO) BSL.ByteString
-- foo name = do
--   tick
--   x <- lift (readTPTPFile name)
--   case x of
--     Nothing -> return BSL.empty
--     Just x -> return x
