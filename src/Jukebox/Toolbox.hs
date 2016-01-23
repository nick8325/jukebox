{-# LANGUAGE RecordWildCards #-}
module Jukebox.Toolbox where

import Jukebox.Options
import Jukebox.Form
import Jukebox.Name
import Jukebox.TPTP.Print
import Control.Monad
import Control.Applicative
import Jukebox.Clausify hiding (run)
import Jukebox.TPTP.ParseProblem
import Jukebox.Monotonox.Monotonicity hiding (guards)
import Jukebox.Monotonox.ToFOF
import System.Exit
import System.IO
import Jukebox.TPTP.FindFile
import Text.PrettyPrint.HughesPJ
import Jukebox.GuessModel
import Jukebox.InferTypes
import Jukebox.TPTP.Parsec hiding (Error, run)
import qualified Jukebox.TPTP.Parsec as Parser
import Jukebox.TPTP.ClauseParser
import Jukebox.TPTP.Lexer hiding (Error, name, Normal)
import qualified Jukebox.TPTP.Lexer as Lexer
import qualified Data.Map.Strict as Map

data GlobalFlags =
  GlobalFlags {
    quiet :: Bool }
  deriving Show

globalFlags :: OptionParser GlobalFlags
globalFlags =
  inGroup "Global options" $
  GlobalFlags <$>
    bool "quiet"
      ["Do not print any informational output.",
       "Default: (off)"]

(=>>=) :: (Monad m, Applicative f) => f (a -> m b) -> f (b -> m c) -> f (a -> m c)
f =>>= g = (>=>) <$> f <*> g
infixl 1 =>>= -- same as >=>

(=>>) :: (Monad m, Applicative f) => f (m a) -> f (m b) -> f (m b)
x =>> y = (>>) <$> x <*> y
infixl 1 =>> -- same as >>

greetingBox :: Tool -> OptionParser (IO ())
greetingBox t = greetingBoxIO t <$> globalFlags

greetingBoxIO :: Tool -> GlobalFlags -> IO ()
greetingBoxIO t GlobalFlags{quiet = quiet} =
  unless quiet $ hPutStrLn stderr (greeting t)

allFilesBox :: OptionParser ((FilePath -> IO ()) -> IO ())
allFilesBox = flip allFiles <$> filenames

allFiles :: (FilePath -> IO ()) -> [FilePath] -> IO ()
allFiles _ [] = do
  hPutStrLn stderr "No input files specified! Try --help."
  exitWith (ExitFailure 1)
allFiles f xs = mapM_ f xs

parseProblemBox :: OptionParser (FilePath -> IO (Problem Form))
parseProblemBox = parseProblemIO <$> findFileFlags

parseProblemIO :: [FilePath] -> FilePath -> IO (Problem Form)
parseProblemIO dirs f = do
  r <- parseProblem dirs f
  case r of
    Left err -> do
      hPutStrLn stderr err
      exitWith (ExitFailure 1)
    Right x -> return x

withString :: (Symbolic a, Pretty a) => String -> (Problem Form -> IO (Problem a)) -> String -> IO String
withString kind f x = do
  let errorAt (UserState _ (At (Lexer.Pos l c) _)) err =
        error $ "At line " ++ show l ++ ", column " ++ show c ++ ": " ++ err
  case run_ (section (const True) <* eof)
            (UserState initialState (scan x)) of
    Ok (UserState (MkState p _) (At _ (Cons Eof _))) Nothing -> do
      let prob = reverse p
      res <- f prob
      return (render (prettyProblem kind Normal res))
    Ok s@(UserState _ (At _ (Cons Eof _))) (Just _) ->
      errorAt s "can't handle include files"
    Ok s _ ->
      errorAt s "lexical error"
    Parser.Error s msg -> errorAt s $ "parse error: " ++ msg
    Expected s exp -> errorAt s $ "parse error: expected " ++ show exp

encodeString :: String -> IO String
encodeString = withString "fof" f
  where
    f = toFofIO globals (return . clausify clFlags) (tags False)
    globals = GlobalFlags { quiet = True }
    clFlags = ClausifyFlags { splitting = False }

clausifyBox :: OptionParser (Problem Form -> IO CNF)
clausifyBox = clausifyIO <$> globalFlags <*> clausifyFlags

clausifyIO :: GlobalFlags -> ClausifyFlags -> Problem Form -> IO CNF
clausifyIO globals flags prob = do
  unless (quiet globals) $ hPutStrLn stderr "Clausifying problem..."
  return $! clausify flags prob

toFofBox :: OptionParser (Problem Form -> IO (Problem Form))
toFofBox = toFofIO <$> globalFlags <*> clausifyBox <*> schemeBox

oneConjectureBox :: OptionParser (CNF -> IO (Problem Clause))
oneConjectureBox = pure oneConjecture

oneConjecture :: CNF -> IO (Problem Clause)
oneConjecture cnf = run cnf f
  where f (CNF cs [cs'] _ _) = return (return (cs ++ cs'))
        f _ = return $ do
          hPutStrLn stderr "Error: more than one conjecture found in input problem"
          exitWith (ExitFailure 1)

toFofIO :: GlobalFlags -> (Problem Form -> IO CNF) -> Scheme -> Problem Form -> IO (Problem Form)
toFofIO globals clausify scheme f = do
  cs <- clausify f >>= oneConjecture
  unless (quiet globals) $ hPutStrLn stderr "Monotonicity analysis..."
  m <- monotone (map what cs)
  let isMonotone ty =
        case Map.lookup ty m of
          Just Nothing -> False
          Just (Just _) -> True
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
monotonicityBox = monotonicity <$> globalFlags

monotonicity :: GlobalFlags -> Problem Clause -> IO String
monotonicity globals cs = do
  unless (quiet globals) $ hPutStrLn stderr "Monotonicity analysis..."
  m <- monotone (map what cs)
  let info (ty, Nothing) = [base ty ++ ": not monotone"]
      info (ty, Just m) =
        [prettyShow ty ++ ": monotone"] ++
        concat
        [ case ext of
             CopyExtend -> []
             TrueExtend -> ["  " ++ base p ++ " true-extended"]
             FalseExtend -> ["  " ++ base p ++ " false-extended"]
        | (p, ext) <- Map.toList m ]

  return (unlines (concat (map info (Map.toList m))))

annotateMonotonicityBox :: OptionParser (Problem Clause -> IO (Problem Clause))
annotateMonotonicityBox = (\globals x -> do
  unless (quiet globals) $ putStrLn "Monotonicity analysis..."
  annotateMonotonicity x) <$> globalFlags

prettyPrintBox :: (Symbolic a, Pretty a) => OptionParser (Problem a -> IO ())
prettyPrintBox = prettyFormIO <$> globalFlags <*> writeFileBox

prettyFormIO :: (Symbolic a, Pretty a) => GlobalFlags -> (String -> IO ()) -> Problem a -> IO ()
prettyFormIO globals write prob
  | isFof prob = prettyPrintIO globals "fof" write prob
  | otherwise = prettyPrintIO globals "tff" write prob

prettyClauseBox :: OptionParser (Problem Clause -> IO ())
prettyClauseBox = f <$> globalFlags <*> writeFileBox
  where
    f globals write cs
      | isFof cs = prettyPrintIO globals "cnf" write cs
      | otherwise = prettyPrintIO globals "tff" write (map (fmap toForm) cs)

prettyPrintIO :: (Symbolic a, Pretty a) => GlobalFlags -> String -> (String -> IO ()) -> Problem a -> IO ()
prettyPrintIO globals kind write prob = do
  unless (quiet globals) $ hPutStrLn stderr "Writing output..."
  write (render (prettyProblem kind Normal prob) ++ "\n")

writeFileBox :: OptionParser (String -> IO ())
writeFileBox =
  flag "output"
    ["Where to write the output.",
     "Default: stdout"]
    putStr
    (fmap myWriteFile argFile)
  where myWriteFile "/dev/null" _ = return ()
        myWriteFile file contents = writeFile file contents

guessModelBox :: OptionParser (Problem Form -> IO (Problem Form))
guessModelBox = guessModelIO <$> expansive <*> universe
  where universe = choose <$>
                   flag "universe"
                   ["Which universe to find the model in.",
                    "Default: peano"]
                   "peano"
                   (argOption ["peano", "trees"])
        choose "peano" = Peano
        choose "trees" = Trees
        expansive = manyFlags "expansive"
                    ["Allow a function to construct 'new' terms in its base base."]
                    (arg "<function>" "expected a function name" Just)

guessModelIO :: [String] -> Universe -> Problem Form -> IO (Problem Form)
guessModelIO expansive univ prob = return (guessModel expansive univ prob)

allObligsBox :: OptionParser ((Problem Clause -> IO Answer) -> CNF -> IO ())
allObligsBox = pure allObligsIO

allObligsIO solve CNF{..} = loop 1 conjectures
  where loop _ [] = result unsatisfiable
        loop i (c:cs) = do
          when multi $ putStrLn $ "Part " ++ part i
          answer <- solve (axioms ++ c)
          when multi $ putStrLn $ "+++ PARTIAL (" ++ part i ++ "): " ++ show answer
          case answer of
            Satisfiable -> result satisfiable
            Unsatisfiable -> loop (i+1) cs
            NoAnswer x -> result (show x)
        multi = length conjectures > 1
        part i = show i ++ "/" ++ show (length conjectures)
        result x = putStrLn ("+++ RESULT: " ++ x)

inferBox :: OptionParser (Problem Clause -> IO (Problem Clause, Type -> Type))
inferBox = (\globals prob -> do
  unless (quiet globals) $ putStrLn "Inferring types..."
  return (run prob inferTypes)) <$> globalFlags

printInferredBox :: OptionParser ((Problem Clause, Type -> Type) -> IO (Problem Clause))
printInferredBox = pure $ \(prob, rep) -> do
  forM_ (types prob) $ \ty ->
    putStrLn $ show ty ++ " => " ++ show (rep ty)
  return prob

equinoxBox :: OptionParser (Problem Clause -> IO Answer)
equinoxBox = pure (\f -> return (NoAnswer GaveUp)) -- A highly sophisticated proof method. We are sure to win CASC! :)
