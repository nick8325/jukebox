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
import Monotonox.ToFOF
import System.Exit
import TPTP.FindFile
import Text.PrettyPrint.HughesPJ

(=>>) :: (Monad m, Applicative f) => f (a -> m b) -> f (b -> m c) -> f (a -> m c)
f =>> g = (>=>) <$> f <*> g
infixl 1 =>> -- same as >=>

allFilesBox :: Tool -> OptionParser ((FilePath -> IO ()) -> IO ())
allFilesBox t = flip (allFiles t) <$> filenames

allFiles :: Tool -> (FilePath -> IO ()) -> [FilePath] -> IO ()
allFiles t _ [] = do
  putStrLn (greeting t)
  putStrLn "No input files specified! Try --help."
  exitWith (ExitFailure 1)
allFiles _ f xs = mapM_ f xs

parseProblemBox :: OptionParser (FilePath -> IO (Problem Form))
parseProblemBox = parseProblemIO <$> findFileFlags

parseProblemIO :: [FilePath] -> FilePath -> IO (Problem Form)
parseProblemIO dirs f = do
  r <- parseProblem dirs f
  case r of
    Left err -> do
      putStrLn err
      exitWith (ExitFailure 1)
    Right x -> return x

clausifyBox :: OptionParser (Problem Form -> IO (Problem Clause))
clausifyBox = clausifyIO <$> clausifyFlags

clausifyIO :: ClausifyFlags -> Problem Form -> IO (Problem Clause)
clausifyIO flags prob = do
  putStrLn "Clausifying problem..."
  let !cs = close (clausify flags prob) (\(cs, css) -> return [ Input (BS.pack "foo") Axiom c | c <- cs ++ concat (take 1 css) ])
  return cs

toFofBox :: OptionParser (Problem Form -> IO (Problem Form))
toFofBox = toFofIO <$> clausifyBox <*> tagsBox

toFofIO :: (Problem Form -> IO (Problem Clause)) -> Scheme -> Problem Form -> IO (Problem Form)
toFofIO clausify scheme f = do
  cs <- clausify f
  m <- monotone (map what (open cs))
  let isMonotone O = True
      isMonotone ty =
        case NameMap.lookup (name ty) m of
          Just (_ ::: Nothing) -> False
          Just (_ ::: Just _) -> True
          Nothing  -> error "Toolbox.toFofIO: type not found (internal error)"
  return (translate scheme isMonotone f)

tagsBox :: OptionParser Scheme
tagsBox = tags <$> tagsFlags

monotonicityBox :: OptionParser (Problem Clause -> IO ())
monotonicityBox = pure monotonicity

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

prettyPrintBox :: (Symbolic a, Pretty a) => String -> OptionParser (Problem a -> IO ())
prettyPrintBox kind = prettyPrintIO kind <$> prettyPrintFlags

prettyPrintFlags =
  flag "output"
    ["Where to write the output.",
     "Default: stdout"]
    putStr
    (fmap writeFile argFile)

prettyPrintIO :: (Symbolic a, Pretty a) => String -> (String -> IO ()) -> Problem a -> IO ()
prettyPrintIO kind write prob = write (render (prettyProblem kind Normal prob) ++ "\n")