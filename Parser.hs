{-# LANGUAGE TypeSynonymInstances, MultiParamTypeClasses #-}
module Parser where

import qualified Lexer as L
import Formula
import Progress
import TPTP
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL
import Text.Parsec hiding (Empty, Error, anyToken)
import Text.Parsec.Error
import Text.Parsec.Pos
import qualified Control.Monad.Trans.Error as E
import Control.Monad.Trans.Class

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

anyToken :: Parser L.Token
anyToken = lift (lift tick) >> tokenPrim show (\_ _ (At pos _) -> sourcePos pos) Just

sourcePos (MkPos file (L.Pos l c)) = newPos file (fromIntegral l) (fromIntegral c)

countTokens :: Parser Int
countTokens = skipMany (anyToken >> modifyState (+1)) >> getState

runParser :: Parser a -> FilePath -> L.TokenStream -> IO (Either ParseError a)
runParser p file ts = do
  let errorT = runParserT p 0 file (nextState file ts [])
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
