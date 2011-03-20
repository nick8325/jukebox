module Main where

import Lexer
import qualified Data.ByteString.Lazy.Char8 as BSL

main = BSL.getContents >>= print . alexScanTokens
