{-# LANGUAGE BangPatterns #-}
module Main where

import Lexer
import Formula
import Parser
import qualified Data.ByteString.Lazy.Char8 as BSL
import System.IO

data Progress a = Tick (Progress a) | Done a

lastAndLength :: TokenStream -> Progress (Token, Int)
lastAndLength = go 0 1
  where go !n 250000 xs = Tick (go n 1 xs)
        go !n t (Cons x Nil) = Done (x, n+1)
        go !n t (Error pos) = Done (error $ "error at " ++ show pos, n+1)
        go !n t (_ `Cons` xs) = go (n+1) (t+1) xs

progress :: String -> Progress a -> IO a
progress msg x = putStr msg >> go 0 x
  where go n x = do
          putStr (spinny n) >> hFlush stdout
          case x of
            Tick x -> go ((n+1) `mod` 4) x
            Done x -> putStrLn "." >> return x
        spinny 0 = ".-\08"
        spinny 1 = "\\\08"
        spinny 2 = "|\08"
        spinny 3 = "/\08"

main = do
  tokens <- fmap scan BSL.getContents
  (last_, length_) <- progress "Lexing..." (lastAndLength tokens)
  putStrLn (show length_ ++ " tokens, last was " ++ show last_)
