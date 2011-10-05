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
import Monotonox.Monotonicity hiding (guards)
import Monotonox.ToFOF
import System.Exit
import TPTP.FindFile
import Text.PrettyPrint.HughesPJ

(=>>=) :: (Monad m, Applicative f) => f (a -> m b) -> f (b -> m c) -> f (a -> m c)
f =>>= g = (>=>) <$> f <*> g
infixl 1 =>>= -- same as >=>

(=>>) :: (Monad m, Applicative f) => f (m a) -> f (m b) -> f (m b)
x =>> y = (>>) <$> x <*> y
infixl 1 =>> -- same as >>

greetingBox :: Tool -> OptionParser (IO ())
greetingBox t = pure (putStrLn (greeting t))

allFilesBox :: OptionParser ((FilePath -> IO ()) -> IO ())
allFilesBox = flip allFiles <$> filenames

allFiles :: (FilePath -> IO ()) -> [FilePath] -> IO ()
allFiles _ [] = do
  putStrLn "No input files specified! Try --help."
  exitWith (ExitFailure 1)
allFiles f xs = mapM_ f xs

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
toFofBox = toFofIO <$> clausifyBox <*> schemeBox

toFofIO :: (Problem Form -> IO (Problem Clause)) -> Scheme -> Problem Form -> IO (Problem Form)
toFofIO clausify scheme f = do
  cs <- clausify f
  putStrLn "Monotonicity analysis..."
  m <- monotone (map what (open cs))
  let isMonotone ty =
        case NameMap.lookup (name ty) m of
          Just (_ ::: Nothing) -> False
          Just (_ ::: Just _) -> True
          Nothing  -> True -- can happen if clausifier removed all clauses about a type
  return (translate scheme isMonotone f)

schemeBox :: OptionParser Scheme
schemeBox =
  choose <$>
  flag "encoding"
    ["Which type encoding to use.",
     "Default: --encoding guards"]
    "guards"
    (argOption ["guards", "tags"])
  <*> tagsFlags
  where choose "guards" flags = guards
        choose "tags" flags = tags flags

monotonicityBox :: OptionParser (Problem Clause -> IO String)
monotonicityBox = pure monotonicity

monotonicity :: Problem Clause -> IO String
monotonicity cs = do
  putStrLn "Monotonicity analysis..."
  m <- monotone (map what (open cs))
  let info (ty ::: Nothing) = [BS.unpack (baseName ty) ++ ": not monotone"]
      info (ty ::: Just m) =
        [prettyShow ty ++ ": monotone"] ++
        concat
        [ case ext of
             CopyExtend -> []
             TrueExtend -> ["  " ++ BS.unpack (baseName p) ++ " true-extended"]
             FalseExtend -> ["  " ++ BS.unpack (baseName p) ++ " false-extended"]
        | p ::: ext <- NameMap.toList m ]

  return (unlines (concat (map info (NameMap.toList m))))

prettyPrintBox :: (Symbolic a, Pretty a) => String -> OptionParser (Problem a -> IO ())
prettyPrintBox kind = prettyPrintIO kind <$> writeFileBox

prettyPrintIO :: (Symbolic a, Pretty a) => String -> (String -> IO ()) -> Problem a -> IO ()
prettyPrintIO kind write prob = write (render (prettyProblem kind Normal prob) ++ "\n")

writeFileBox :: OptionParser (String -> IO ())
writeFileBox =
  flag "output"
    ["Where to write the output.",
     "Default: stdout"]
    putStr
    (fmap writeFile argFile)