{-# LANGUAGE BangPatterns #-}
module Main where

import Lexer
import qualified Data.ByteString.Lazy.Char8 as BSL

lastAndLength :: [a] -> (a, Int)
lastAndLength = go 0
  where go !n [x] = (x, n+1)
        go !n (_:xs) = go (n+1) xs

main = do
  tokens <- fmap alexScanTokens BSL.getContents
  let (last_, length_) = lastAndLength tokens
  putStrLn (show length_ ++ " tokens, last was " ++ show last_)
