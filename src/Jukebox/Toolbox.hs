-- Components ("boxes") which can be put together to make tools.
{-# LANGUAGE RecordWildCards, CPP #-}
module Jukebox.Toolbox where

import Jukebox.Options
import Jukebox.Form
import Jukebox.Name
import Jukebox.TPTP.Print
import Control.Monad
import Jukebox.TPTP.Parse
import Jukebox.Tools.Clausify hiding (run)
import Jukebox.Tools.AnalyseMonotonicity hiding (guards)
import Jukebox.Tools.EncodeTypes
import Jukebox.Tools.GuessModel
import Jukebox.Tools.InferTypes
import System.Exit
import System.IO
import Jukebox.TPTP.FindFile
import qualified Data.Map.Strict as Map
import qualified Jukebox.SMTLIB as SMT
#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif
import Data.IORef

----------------------------------------------------------------------
-- Some standard flags.

data GlobalFlags =
  GlobalFlags {
    quiet :: Bool }
  deriving Show

globalFlags :: OptionParser GlobalFlags
globalFlags =
  inGroup "Output options" $
  GlobalFlags <$>
    -- Use flag rather than bool to avoid getting a --no-quiet option in the
    -- help message
    flag "quiet"
      ["Only print essential information."]
      False (pure True)

data TSTPFlags =
  TSTPFlags {
    tstp :: Bool }
  deriving Show

tstpFlags :: OptionParser TSTPFlags
tstpFlags =
  inGroup "Output options" $
  TSTPFlags <$>
    bool "tstp"
      ["Produce TSTP-compatible output (off by default)."]
      False

----------------------------------------------------------------------
-- Printing output messages.

-- Print a message as a TPTP comment.
comment :: String -> IO ()
comment msg = mapM_ putStrLn ["% " ++ line | line <- lines msg]

-- Do something only when output is enabled.
quietly :: GlobalFlags -> IO () -> IO ()
quietly globals action = unless (quiet globals) action

----------------------------------------------------------------------
-- Combinators for boxes.

-- Boxes typically have the type OptionParser (a -> IO b).
-- The following two combinators chain boxes together.
(=>>=) :: OptionParser (a -> IO b) -> OptionParser (b -> IO c) -> OptionParser (a -> IO c)
f =>>= g = (>=>) <$> f <*> g
infixl 1 =>>= -- same fixity as >=>

(=>>) :: OptionParser (IO a) -> OptionParser (IO b) -> OptionParser (IO b)
x =>> y = (>>) <$> x <*> y
infixl 1 =>> -- same fixity as >>

----------------------------------------------------------------------
-- Process all files that were passed in on the command line.

forAllFilesBox :: OptionParser ((FilePath -> IO ()) -> IO ())
forAllFilesBox = forAllFiles <$> filenames

forAllFiles :: [FilePath] -> (FilePath -> IO ()) -> IO ()
forAllFiles [] _ = do
  hPutStrLn stderr "No input files specified! Try --help."
  hPutStrLn stderr "You can use \"-\" to read from standard input."
  exitWith (ExitFailure 1)
forAllFiles xs f = mapM_ f xs

----------------------------------------------------------------------
-- Read in a single problem.

readProblemBox :: OptionParser (FilePath -> IO (Problem Form))
readProblemBox = readProblem <$> findFileFlags

readProblem :: [FilePath] -> FilePath -> IO (Problem Form)
readProblem dirs f = do
  r <- parseProblem dirs f
  case r of
    Left err -> do
      hPutStrLn stderr err
      exitWith (ExitFailure 1)
    Right x -> return x

----------------------------------------------------------------------
-- Write output to a file.

printProblemBox :: OptionParser (Problem Form -> IO ())
printProblemBox = prettyPrintIO showProblem <$> writeFileBox

printProblemSMTBox :: OptionParser (Problem Form -> IO ())
printProblemSMTBox = prettyPrintIO SMT.showProblem <$> writeFileBox

printClausesBox :: OptionParser (Problem Clause -> IO ())
printClausesBox = prettyPrintIO showClauses <$> writeFileBox

prettyPrintIO :: (a -> String) -> (String -> IO ()) -> a -> IO ()
prettyPrintIO shw write prob = do
  write (shw prob ++ "\n")

writeFileBox :: OptionParser (String -> IO ())
writeFileBox =
  inGroup "Output options" $
  flag "output"
    ["Where to write the output file (stdout by default)."]
    putStr
    (fmap myWriteFile argFile)
  where myWriteFile "/dev/null" _ = return ()
        myWriteFile "-" contents = putStr contents
        myWriteFile file contents = writeFile file contents

----------------------------------------------------------------------
-- Clausify a problem.

clausifyBox :: OptionParser (Problem Form -> IO CNF)
clausifyBox =
  (\flags prob -> return $! clausify flags prob) <$> clausifyFlags

----------------------------------------------------------------------
-- Make sure that the problem only has one conjecture.

oneConjectureBox :: OptionParser (CNF -> IO (Problem Clause))
oneConjectureBox = oneConjecture <$> flags
  where
    flags =
      inGroup "Input and clausifier options" $
      flag "conjecture"
        ["If the problem has multiple conjectures, take only this one.",
         "Conjectures are numbered from 1."]
        Nothing (Just <$> argNum)

oneConjecture :: Maybe Int -> CNF -> IO (Problem Clause)
oneConjecture conj cnf =
  run cnf $ \(CNF axioms obligs _ _) ->
    case conj of
      Just n ->
        if n <= length obligs then choose axioms (obligs !! (n-1))
        else err ["Conjecture number out of bounds:",
                  "problem after clausification has " ++ show (length obligs) ++ " conjectures"]
      Nothing ->
        case obligs of
          [cs] -> choose axioms cs
          _ ->
            err ["Can't handle more than one conjecture in input problem!",
                 "This problem has " ++ show (length obligs) ++ " conjectures.",
                 "Try using the --conjecture flag."]
  where
    err msgs = return $ do
      mapM_ (hPutStrLn stderr) msgs
      exitWith (ExitFailure 1)

    choose axioms cs = return (return (axioms ++ cs))

----------------------------------------------------------------------
-- Solve all conjectures in a problem and report the final SZS status.

-- A solver is given a problem in CNF and should return an answer.
--
-- It is also given a function of type IO () -> IO ().
-- Wrapping an action in this function delays the action until after
-- the answer is printed; this can be useful for e.g. printing a proof
-- when the prover might be running under a timeout.
type Solver = (IO () -> IO ()) -> Problem Clause -> IO Answer

forAllConjecturesBox :: OptionParser (Solver -> CNF -> IO ())
forAllConjecturesBox = forAllConjectures <$> tstpFlags

forAllConjectures :: TSTPFlags -> Solver -> CNF -> IO ()
forAllConjectures (TSTPFlags tstp) solve CNF{..} = do
  todo <- newIORef (return ())
  loop 1 todo conjectures
  where loop _ todo [] =
          result todo unsatisfiable
        loop i todo (c:cs) = do
          when multi $ do
            join (readIORef todo)
            writeIORef todo (return ())
          answer <- solve (\x -> modifyIORef todo (>> x)) (axioms ++ c)
          when multi $ do
            putStrLn $ "Partial result (" ++ part i ++ "): " ++ show answer
            putStrLn ""
          case answer of
            Sat _ -> result todo satisfiable
            Unsat _ -> loop (i+1) todo cs
            NoAnswer x -> result todo (NoAnswer x)
        multi = length conjectures > 1
        part i = show i ++ "/" ++ show (length conjectures)
        result todo x = do
          when tstp $ do
            putStrLn ("% SZS status " ++ show x)
            putStrLn ""
          join (readIORef todo)
          putStrLn ("RESULT: " ++ show x ++ " (" ++ explainAnswer x ++ ").")

----------------------------------------------------------------------
-- Convert a problem from TFF to FOF.

toFofBox :: OptionParser (Problem Form -> IO (Problem Form))
toFofBox = toFof <$> clausifyBox <*> schemeBox

toFof :: (Problem Form -> IO CNF) -> Scheme -> Problem Form -> IO (Problem Form)
toFof clausify scheme f = do
  CNF{..} <- clausify f
  -- In some cases we might get better results by considering each
  -- problem (axioms + conjecture) separately, but no big deal.
  m <- monotone (map what (axioms ++ concat conjectures))
  let isMonotone ty =
        case Map.lookup ty m of
          Just Nothing -> False
          Just (Just _) -> True
          Nothing  -> True -- can happen if clausifier removed all clauses about a type
  return (translate scheme isMonotone f)

schemeBox :: OptionParser Scheme
schemeBox =
  inGroup "Options for encoding types" $
  choose <$>
  flag "encoding"
    ["Which type encoding to use (guards by default)."]
    "guards"
    (argOption ["guards", "tags"])
  <*> tagsFlags
  where choose "guards" _flags = guards
        choose "tags" flags = tags flags

----------------------------------------------------------------------
-- Analyse monotonicity.

-- Annotate types with monotonicity information.
annotateMonotonicityBox :: OptionParser (Problem Clause -> IO (Problem Clause))
annotateMonotonicityBox = pure annotateMonotonicity

showMonotonicityBox :: OptionParser (Problem Clause -> IO String)
showMonotonicityBox =
  pure $ \cs -> do
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

----------------------------------------------------------------------
-- Guess an infinite model.

guessModelBox :: OptionParser (Problem Form -> IO (Problem Form))
guessModelBox =
  inGroup "Options for the model guesser:" $
  (\expansive univ prob -> return (guessModel expansive univ prob))
    <$> expansive <*> universe
  where universe = choose <$>
                   flag "universe"
                   ["Which universe to find the model in (peano by default)."]
                   "peano"
                   (argOption ["peano", "trees"])
        choose "peano" = Peano
        choose "trees" = Trees
        expansive = manyFlags "expansive"
                    ["Allow a function to construct 'new' terms in its base case."]
                    (arg "<function>" "expected a function name" Just)

----------------------------------------------------------------------
-- Infer types.

inferBox :: OptionParser (Problem Clause -> IO (Problem Clause, Type -> Type))
inferBox = pure (\prob -> return (run prob inferTypes))

printInferredBox :: OptionParser ((Problem Clause, Type -> Type) -> IO (Problem Clause))
printInferredBox = pure $ \(prob, rep) -> do
  forM_ (types prob) $ \ty ->
    putStrLn $ show ty ++ " => " ++ show (rep ty)
  return prob
