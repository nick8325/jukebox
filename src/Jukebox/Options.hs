-- Command-line option parsing using applicative functors.
-- Parsers are represented as values of type OptionParser a,
-- and run using the function
--   parseCommandLine :: String -> OptionParser a -> IO a.
-- OptionParsers are built from ArgParsers, which parse a single
-- option (e.g. --verbosity 3).

{-# LANGUAGE FlexibleContexts, CPP #-}
module Jukebox.Options where

import Data.Char
import Data.List
import System.Environment
import System.Exit
import System.IO
#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
import Data.Monoid
#endif

----------------------------------------------------------------------
-- A parser of some kind annotated with a help text of some kind
data Annotated d p a = Annotated
  { descr :: d,
    parser :: p a }

instance Functor p => Functor (Annotated d p) where
  fmap f (Annotated d x) = Annotated d (fmap f x)

instance (Monoid d, Applicative p) => Applicative (Annotated d p) where
  pure = Annotated mempty . pure
  Annotated d f <*> Annotated d' x =
    Annotated (d `mappend` d') (f <*> x)

instance (Monoid d, Monoid (p a)) => Monoid (Annotated d p a) where
  mempty = Annotated mempty mempty
  Annotated d p `mappend` Annotated d' p' =
    Annotated (d `mappend` d') (p `mappend` p')

----------------------------------------------------------------------
-- The ArgParser type: parsing of single flags.

type ArgParser = Annotated [String] SeqParser
  -- annotated with a description, e.g. "<number>"

-- Called SeqParser because <*> is sequential composition.
data SeqParser a = SeqParser
  { args :: Int, -- How many arguments will be consumed
    consume :: [String] -> Either Error a }

instance Functor SeqParser where
  fmap f (SeqParser a c) = SeqParser a (fmap f . c)

instance Applicative SeqParser where
  pure = SeqParser 0 . const . pure
  SeqParser a c <*> SeqParser a' c' = SeqParser (a + a') f
    where f xs = c xs <*> c' (drop a xs)

----------------------------------------------------------------------
-- Combinators for building ArgParsers.

arg :: String -> String -> (String -> Maybe a) -> ArgParser a
arg desc err f = Annotated [desc] (SeqParser 1 c)
  where c [] = Left (Mistake err)
        c (x:_) | "-" `isPrefixOf` x = Left (Mistake err)
        c (x:_) =
          case f x of
            Nothing -> Left (Mistake err)
            Just ok -> Right ok

argNum :: (Read a, Num a) => ArgParser a
argNum = arg "<num>" "expected a number" f
  where f x =
          case reads x of
            [(y, "")] -> Just y
            _ -> Nothing

argFile :: ArgParser FilePath
argFile = arg "<file>" "expected a file" Just

argFiles :: ArgParser [FilePath]
argFiles = arg "<files>" "expected a list of files" $ \x ->
  Just $ elts $ x ++ ","
  where
    elts [] = []
    elts s  = w:elts r
      where
        w = takeWhile (/= ',') s
        r = tail (dropWhile (/= ',') s)

argName :: ArgParser String
argName = arg "<name>" "expected a name" Just

argNums :: ArgParser [Int]
argNums = arg "<nums>" "expected a number list" $ \x ->
  nums . groupBy (\x y -> isDigit x == isDigit y) $ x ++ ","
  where
    nums []                = Just []
    nums (n:",":ns)        = (read n :) `fmap` nums ns
    nums (n:"..":m:",":ns) = ([read n .. read m] ++) `fmap` nums ns
    nums _                 = Nothing

argOption :: [(String, a)] -> ArgParser a
argOption as =
  argOptionWith "one" "or" "" (map fst as) (`lookup` as)

argList :: [String] -> ArgParser [String]
argList as =
  argOptionWith "several" "and" "*" as $ \x -> elts (x ++ ",")
  where
    elts []              = Just []
    elts s | w `elem` as = (w:) `fmap` elts r
      where
        w = takeWhile (/= ',') s
        r = tail (dropWhile (/= ',') s)
    
    elts _ = Nothing

argOptionWith :: String -> String -> String -> [String] -> (String -> Maybe a) -> ArgParser a
argOptionWith one or suff opts p =
  arg ("<" ++ intercalate " | " opts ++ ">" ++ suff)
    ("expected " ++ one ++ " of " ++ list) p
  where
    list =
      case opts of
        [] -> "<empty list>" -- ??
        _ ->
          intercalate ", " (init opts) ++ " " ++ or ++ " " ++ last opts

-- A parser that always fails but produces an error message (useful for --help etc.)
argUsage :: ExitCode -> [String] -> ArgParser a
argUsage code err = Annotated [] (SeqParser 0 (const (Left (Usage code err))))

----------------------------------------------------------------------
-- The OptionParser type: parsing of whole command lines.

type OptionParser = Annotated [Flag] ParParser

-- The help information for a flag.
data Flag = Flag
  { flagName :: String,
    flagGroup :: String,
    flagMode :: FlagMode,
    flagHelp :: [String],
    flagArgs :: String } deriving (Eq, Show)
data FlagMode = NormalMode | ExpertMode | HiddenMode deriving (Eq, Show)

flagExpert :: Flag -> Bool
flagExpert f = flagMode f == ExpertMode

-- Called ParParser because <*> is parallel composition.
-- In other words, in f <*> x, f and x both see the whole command line.
-- We want this when parsing command lines because
-- it doesn't matter what order we write the options in,
-- and because f and x might understand the same flags.
data ParParser a = ParParser
  { val :: IO a, -- impure so we can put system information in our options records
    peek :: [String] -> ParseResult a }

data ParseResult a
    -- Yes n x: consumed n arguments, continue parsing with x
  = Yes Int (ParParser a)
    -- No x: didn't understand this flag, continue parsing with x
  | No (ParParser a)
    -- Error
  | Error Error

data Error =
    Mistake String
  | Usage ExitCode [String]

instance Functor ParParser where
  fmap f x = pure f <*> x

instance Applicative ParParser where
  pure x = ParParser (return x) (const (pure x))
  ParParser v p <*> ParParser v' p' =
    ParParser (v <*> v') (\xs -> p xs <*> p' xs)

instance Functor ParseResult where
  fmap f x = pure f <*> x

instance Applicative ParseResult where
  pure = No . pure
  Yes n r <*> Yes n' r'
    | n == n' = Yes n (r <*> r')
    | otherwise = error "Options.ParseResult: inconsistent number of arguments"
  Error s <*> _ = Error s
  _ <*> Error s = Error s
  Yes n r <*> No x = Yes n (r <*> x)
  No x <*> Yes n r = Yes n (x <*> r)
  No f <*> No x = No (f <*> x)

runPar :: ParParser a -> [String] -> Either Error (IO a)
runPar p [] = Right (val p)
runPar p xs@(x:_) =
  case peek p xs of
    Yes n p' -> runPar p' (drop n xs)
    No _ -> Left (Mistake ("Didn't recognise option " ++ x))
    Error err -> Left err

await :: (String -> Bool) -> a -> (String -> [String] -> ParseResult a) -> ParParser a
await p def par = ParParser (return def) f
  where f (x:xs) | p x =
          case par x xs of
            Yes n r -> Yes (n+1) r
            No _ ->
              error "Options.await: got No"
            Error err -> Error err
        f _ = No (await p def par)

----------------------------------------------------------------------
-- Low-level primitives for building OptionParsers.

-- Produce an OptionParser with maximum flexibility.
primFlag ::
  -- Name and description of options (for documentation)
  String -> [String] ->
  -- Predicate which checks if this argument is our option
  (String -> Bool) ->
  -- Handle repeated occurrences of the same option
  (a -> a -> Either Error a) ->
  -- Default argument value and argument parser
  -- The argument parser is given the option name.
  a -> ArgParser (String -> a) -> OptionParser a
primFlag name help p combine def (Annotated desc (SeqParser args f)) =
  Annotated [desc'] (await p def (g Right))
  where desc' = Flag name "General options" NormalMode help (unwords desc)
        g comb x xs =
          case f xs >>= comb . ($ x) of
            Left (Mistake err) -> Error (Mistake ("Error in option --" ++ name ++ ": " ++ err))
            Left (Usage code err) -> Error (Usage code err)
            Right y ->
              Yes args (await p y (g (combine y)))

----------------------------------------------------------------------
-- Combinators for building OptionParsers.

-- From a flag name and description and argument parser, produce an OptionParser.
flag :: String -> [String] -> a -> ArgParser a -> OptionParser a
flag name help def p =
  primFlag name help
    (\x -> x == "--" ++ name)
    (\_ y -> return y) -- take second occurrence of flag
    def (const <$> p)

-- A variant of 'flag' that allows repeated flags.
manyFlags :: String -> [String] -> ArgParser a -> OptionParser [a]
manyFlags name help p =
  primFlag name help
    (\x -> x == "--" ++ name)
    (\x y -> return (x ++ y))
    [] (const <$> return <$> p)

-- A boolean flag.
bool :: String -> [String] -> Bool -> OptionParser Bool
bool name help def =
  primFlag ("(no-)" ++ name) help
    (\x -> x `elem` ["--" ++ name, "--no-" ++ name])
    (\_ y -> return y)
    def
    (pure (\name' -> if "--" ++ name == name' then True else False))

-- A parser that reads all file names from the command line.
filenames :: OptionParser [String]
filenames = Annotated [] (from [])
  where from xs = await p xs (f xs)
        p x = not ("-" `isPrefixOf` x) || x == "-"
        f xs y _ = Yes 0 (from (xs ++ [y]))

-- Take a value from the environment.
io :: IO a -> OptionParser a
io m = Annotated [] p
  where p = ParParser m (const (No p))

-- Change the group associated with a set of flags.
inGroup :: String -> OptionParser a -> OptionParser a
inGroup x (Annotated fls f) = Annotated [fl{ flagGroup = x } | fl <- fls] f

-- Mark a flag as being for experts only.
expert :: OptionParser a -> OptionParser a
expert (Annotated fls f) = Annotated [fl{ flagMode = ExpertMode } | fl <- fls] f

-- Mark a flag as being hidden.
hidden :: OptionParser a -> OptionParser a
hidden (Annotated fls f) = Annotated [fl{ flagMode = HiddenMode } | fl <- fls] f

-- Add a --version flag.
version :: String -> OptionParser a -> OptionParser a
version x p =
  p <*
    inGroup "Miscellaneous options"
      (flag "version" ["Show the version number."] ()
        (argUsage ExitSuccess [x]))

----------------------------------------------------------------------
-- Help screens, error messages and so on.

printHelp :: ExitCode -> [String] -> IO a
printHelp code xs = do
  mapM_ (hPutStrLn stderr) xs
  exitWith code

printError :: String -> String -> IO a
printError name err =
  printHelp (ExitFailure 1) $
    [err ++ ".", "Try " ++ name ++ " --help."]

help :: String -> String -> OptionParser a -> OptionParser a
help name description p = p'
  where
    p' =
      p <*
        (inGroup "Miscellaneous options" $
         flag "help" ["Show help text."] ()
        
           (argUsage ExitSuccess (helpText False name description p')))
        <*
        (if any flagExpert (descr p) then
          (inGroup "Miscellaneous options" $
           flag "expert-help" ["Show help text for hidden options."] ()
             (argUsage ExitSuccess (helpText True name description p')))
         else pure ())

usageText :: String -> String -> [String]
usageText name descr =
  [descr ++ ".",
   "Usage: " ++ name ++ " <option>* <file>*, where <file> is in TPTP format."]

helpText :: Bool -> String -> String -> OptionParser a -> [String]
helpText expert name description p =
  intercalate [""] $
    [usageText name description] ++
    [[flagGroup f0 ++ ":"] ++
     concat [justify ("--" ++ flagName f ++ " " ++ flagArgs f) (flagHelp f) | f <- fs]
     | fs@(f0:_) <- groups (filter ok (nub (descr p))) ] ++
    [ ["To see hidden options too, try --expert-help."]
    | any flagExpert (descr p), not expert ]
  where
    groups [] = []
    groups (f:fs) =
      (f:[f' | f' <- fs, flagGroup f == flagGroup f']):
      groups [f' | f' <- fs, flagGroup f /= flagGroup f']
    ok flag =
      case flagMode flag of
        NormalMode -> True
        ExpertMode -> expert
        HiddenMode -> False

justify :: String -> [String] -> [String]
justify name help = ["  " ++ name] ++ map ("    " ++) help

----------------------------------------------------------------------
-- Running the parser.

parseCommandLine :: String -> OptionParser a -> IO a
parseCommandLine description p =
  parseCommandLineWithExtraArgs [] description p

parseCommandLineWithExtraArgs :: [String] -> String -> OptionParser a -> IO a
parseCommandLineWithExtraArgs args0 description p = do
  name <- getProgName
  args <- getArgs
  parseCommandLineWithArgs name (args0 ++ args) description p

parseCommandLineWithArgs :: String -> [String] -> String -> OptionParser a -> IO a
parseCommandLineWithArgs name args description p = do
  case runPar (parser (help name description p)) args of
    Left (Mistake err) -> printError name err
    Left (Usage code err) -> printHelp code err
    Right x -> x
