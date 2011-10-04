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

monotonox = Tool "Monotonox" "1" "Monotonicity analysis"
jukebox = Tool "Jukebox" "1" undefined

tools = tool monotonox pipeline

allFiles :: Tool -> (FilePath -> IO ()) -> [FilePath] -> IO ()
allFiles t _ [] = do
  putStrLn (greeting t)
  putStrLn "No input files specified! Try --help."
  exitWith (ExitFailure 1)
allFiles _ f xs = mapM_ f xs

parseProblemIO :: [FilePath] -> FilePath -> IO (Problem Form)
parseProblemIO dirs f = do
  r <- parseProblem dirs f
  case r of
    Left err -> do
      putStrLn err
      exitWith (ExitFailure 1)
    Right x -> return x

clausifyIO :: ClausifyFlags -> Problem Form -> IO (Problem Clause)
clausifyIO flags prob = do
  putStrLn "Clausifying problem..."
  let !cs = close (clausify flags prob) (\(cs, css) -> return [ Input (BS.pack "foo") Axiom c | c <- cs ++ concat (take 1 css) ])
  return cs

monotonicity :: Problem Clause -> IO ()
monotonicity cs = do
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

pipeline :: OptionParser (IO ())
pipeline =
  allFiles monotonox <$>
  (compose3 <$> (parseProblemIO <$> findFileFlags)
            <*> (clausifyIO <$> clausifyFlags)
            <*> pure monotonicity) <*> filenames
    where compose3 f g h x = f x >>= g >>= h

main = join (parseCommandLine jukebox tools)