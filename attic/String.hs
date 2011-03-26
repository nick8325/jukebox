{-# OPTIONS_GHC -O2 #-}
{-# LANGUAGE BangPatterns,TemplateHaskell #-}
module String(Str, string, stringLit, unstring) where

import Data.Word
import Data.Bits
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import Data.ByteString.Unsafe
import Data.ByteString.Internal
import Language.Haskell.TH

-- Strings with efficient comparison.
--
-- Stored as a pair of a Word and a ByteString.
-- The Word is the middle four bytes of the string,
-- ORed with 2^(wordSize-1) if the string is longer than four bytes.
-- If the string is not longer than four bytes, we store the empty string.
--
-- Thus, if the hashes are different then so are the strings;
-- if the hashes are the same and the highest bit is not set then the strings are the same
-- (and no more than four bytes long);
-- if the hashes are the same and the highest bit is set then the strings might still differ.
--
-- This means that comparing against a short string is just an integer
-- compare. What's nice is that if one of the strings is known at
-- compile-time and short (say, it's a particular token), then the
-- comparison compiles down to an integer compare too.
data Str = Str {-# UNPACK #-} !Int {-# UNPACK #-} !BS.ByteString

instance Eq Str where
  Str h1 s1 == Str h2 s2 | h1 /= h2 = False
                         | h1 < 0 = bsEq s1 s2
                         | otherwise = True

{-# NOINLINE bsEq #-}
bsEq :: BS.ByteString -> BS.ByteString -> Bool
bsEq !s1 !s2 = s1 == s2

instance Ord Str where
  Str h1 s1 `compare` Str h2 s2 =
    case h1 `compare` h2 of
      EQ | h1 < 0 -> bsCompare s1 s2
         | otherwise -> EQ
      x -> x

{-# NOINLINE bsCompare #-}
bsCompare :: BS.ByteString -> BS.ByteString -> Ordering
bsCompare !s1 !s2 = s1 `compare` s2

instance Show Str where
  show = BSC.unpack . unstring

string :: BS.ByteString -> Str
string s =
  let word :: Word
      word = undefined

      !hashBytes | bitSize word == 32 = 4
                 | bitSize word == 64 = 8 
                 | otherwise = bitSize word `div` 8

      get :: Int -> Word
      get = fromIntegral . unsafeIndex s in
  case BS.length s of
    0 -> Str 0 BS.empty
    1 -> Str (fromIntegral (get 0)) BS.empty
    2 -> Str (fromIntegral (get 0 .|. (get 1 `shiftL` 8))) BS.empty 
    _ | BS.length s <= hashBytes ->
        Str (fromIntegral (BS.foldr' op 0 s)) BS.empty
      | otherwise ->
        Str (fromIntegral (BS.foldr' op 0 middle `setBit` (bitSize word-1))) s
          where op :: Word8 -> Word -> Word
                op c x = (x `shiftL` 8) .|. fromIntegral c
                middle = unsafeTake hashBytes (unsafeDrop ((BS.length s - hashBytes) `shiftR` 1) s)

unstring :: Str -> BS.ByteString
unstring (Str hash s) | hash `testBit` (bitSize hash-1) = s
                      | otherwise = BS.pack (loop hash)
  where loop 0 = []
        loop n = toEnum (n `mod` 256):loop (n `div` 256)

stringLit :: String -> ExpQ
stringLit xs =
  let Str hash s = string (BSC.pack xs)
      len = BS.length s
      addr = LitE (StringPrimL (BSC.unpack s))
  in
    if BSC.null s then [| Str hash BS.empty |]
    else [| Str hash (inlinePerformIO (unsafePackAddressLen len $(return addr))) |]
