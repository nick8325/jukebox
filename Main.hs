{-# LANGUAGE BangPatterns #-}
module Main where

import TPTP.ParseProblem
import System.Environment
import Form
-- import InferTypes
import TPTP.Print
import Name
import Text.PrettyPrint.HughesPJ
import Clausify
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL
import Control.Monad
import Monotonox.Monotonicity
import NameMap
import TPTP.Binary
import TPTP.FindFile
import Options
import Control.Applicative
import System.Exit

data Flags = Flags ClausifyFlags [FilePath] [FilePath] deriving Show

flags = Flags <$> clausifyFlags <*> findFileFlags <*> filenames
monotonox = Tool "Monotonox" "1" "Monotonicity analysis"
jukebox = Tool "Jukebox" "1" undefined

tools = tool monotonox flags

main = do
  fl@(Flags cl ff args) <- parseCommandLine jukebox tools
  when (null args) $ do
    putStrLn (greeting monotonox)
    putStrLn "No input files specified! Try --help."
    exitWith (ExitFailure 1)
  print fl
  forM_ args $ \arg -> do
    res <- parseProblem ff arg
    case res of
      Left err -> putStrLn err
      Right p -> do
        -- let ?monotone = const Infinite
        --     ?size = const Infinite
        -- in putStrLn (prettyShow (infer p))
        putStrLn "Clausifying problem..."
        let !cs = close (clausify cl p) (\(cs, css) -> return [ Input (BS.pack "foo") Axiom c | c <- cs ++ concat (take 1 css) ])
        return ()
        putStrLn "Writing clauses..."
        BSL.writeFile (arg ++ ".clauses") (encode cs)
        putStrLn "Reading clauses..."
        !cs <- fmap decode (BSL.readFile (arg ++ ".clauses"))
        putStrLn "Monotonicity analysis..."
        m <- monotone (map what (open cs))
        forM_ (NameMap.toList m) $ \(ty ::: x) ->
          case x of
            Nothing -> putStrLn (BS.unpack (baseName ty) ++ ": not monotone")
            Just m -> do
              putStrLn (prettyShow ty ++ ": monotone")
              forM_ (NameMap.toList m) $ \(p ::: ext) ->
                case ext of
                  CopyExtend -> return ()
                  TrueExtend -> putStrLn ("  " ++ BS.unpack (baseName p) ++ " true-extended")
                  FalseExtend -> putStrLn ("  " ++ BS.unpack (baseName p) ++ " false-extended")
        -- putStrLn (render (prettyProblem "tff" Normal p))
        -- putStrLn (render (prettyProblem "tff" Normal cs))
        -- putStrLn (render (prettyProblem "tff" Chatty p))
        -- putStrLn (render (prettyProblem "tff" Chatty cs))
