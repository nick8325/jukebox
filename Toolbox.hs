module Toolbox where

import Options
import qualified Data.ByteString.Char8 as BS
import Form
import Name
import qualified NameMap
import TPTP.Print
import Control.Monad
import Control.Applicative
import Clausify
import TPTP.ParseProblem
import Monotonox.Monotonicity
import System.Exit
import TPTP.FindFile

(=>>) :: (Monad m, Applicative f) => f (a -> m b) -> f (b -> m c) -> f (a -> m c)
f =>> g = (>=>) <$> f <*> g
infixl 1 =>> -- same as >=>

allFilesTool :: Tool -> OptionParser ((FilePath -> IO ()) -> IO ())
allFilesTool t = flip (allFiles t) <$> filenames

allFiles :: Tool -> (FilePath -> IO ()) -> [FilePath] -> IO ()
allFiles t _ [] = do
  putStrLn (greeting t)
  putStrLn "No input files specified! Try --help."
  exitWith (ExitFailure 1)
allFiles _ f xs = mapM_ f xs

parseProblemTool :: OptionParser (FilePath -> IO (Problem Form))
parseProblemTool = parseProblemIO <$> findFileFlags

parseProblemIO :: [FilePath] -> FilePath -> IO (Problem Form)
parseProblemIO dirs f = do
  r <- parseProblem dirs f
  case r of
    Left err -> do
      putStrLn err
      exitWith (ExitFailure 1)
    Right x -> return x

clausifyTool :: OptionParser (Problem Form -> IO (Problem Clause))
clausifyTool = clausifyIO <$> clausifyFlags

clausifyIO :: ClausifyFlags -> Problem Form -> IO (Problem Clause)
clausifyIO flags prob = do
  putStrLn "Clausifying problem..."
  let !cs = close (clausify flags prob) (\(cs, css) -> return [ Input (BS.pack "foo") Axiom c | c <- cs ++ concat (take 1 css) ])
  return cs

monotonicityTool :: OptionParser (Problem Clause -> IO ())
monotonicityTool = pure monotonicity

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