module Main where

import Lexer
import qualified Data.ByteString.Lazy.Char8 as BSL

main = do
  tokens <- fmap alexScanTokens BSL.getContents
  putStrLn (show (length tokens) ++ " tokens, last was " ++ show (last tokens))
