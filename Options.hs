{-# LANGUAGE FlexibleContexts #-}
module Options where

import Control.Applicative
import Control.Monad(mplus)
import Data.Char
import Data.List
import Data.Monoid
import System.Environment
import System.Exit

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
-- Parsing of single arguments (e.g. integers)
-- and single flags (e.g. --verbosity 3).

type ArgParser = Annotated ArgDesc SeqParser
type ArgDesc = String -- description, e.g. "<number>"

-- Called SeqParser because <*> is sequential composition.
data SeqParser a = SeqParser
  { args :: Int, -- How many arguments will be consumed
    consume :: [String] -> Either String a }

instance Functor SeqParser where
  fmap f (SeqParser a c) = SeqParser a (fmap f . c)

instance Applicative SeqParser where
  pure = SeqParser 0 . const . pure
  SeqParser a c <*> SeqParser a' c' = SeqParser (a + a') f
    where f xs = c xs <*> c' (drop a xs)

arg :: ArgDesc -> String -> (String -> Maybe a) -> ArgParser a
arg desc err f = Annotated desc (SeqParser 1 c)
  where c [] = Left err
        c (x:_) | "--" `isPrefixOf` x = Left err
        c (x:_) =
          case f x of
            Nothing -> Left err
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

argName :: ArgParser FilePath
argName = arg "<name>" "expected a name" Just

argNums :: ArgParser [Int]
argNums = arg "<nums>" "expected a number list" $ \x ->
  nums . groupBy (\x y -> isDigit x == isDigit y) $ x ++ ","
  where
    nums []                = Just []
    nums (n:",":ns)        = (read n :) `fmap` nums ns
    nums (n:"..":m:",":ns) = ([read n .. read m] ++) `fmap` nums ns
    nums _                 = Nothing

argOption :: [String] -> ArgParser String
argOption as = arg ("<" ++ concat (intersperse " | " as) ++ ">") "expected an argument" elts
  where
    elts x | x `elem` as = Just x
           | otherwise   = Nothing

argList :: [String] -> ArgParser [String]
argList as = arg ("<" ++ concat (intersperse " | " as) ++ ">*") "expected an argument" $ \x ->
  elts $ x ++ ","
  where
    elts []              = Just []
    elts s | w `elem` as = (w:) `fmap` elts r
      where
        w = takeWhile (/= ',') s
        r = tail (dropWhile (/= ',') s)
    
    elts _ = Nothing

----------------------------------------------------------------------
-- Parsing of whole command lines.

type OptionParser = Annotated [Flag] ParParser

-- Called ParParser because <*> is parallel composition.
-- In other words, in f <*> x, f and x both see the whole command line.
-- We want this when parsing command lines because
-- it doesn't matter what order we write the options in.
data ParParser a = ParParser
  { val :: IO a, -- impure so we can put system information in our options records
    peek :: [String] -> ParseResult a }

data ParseResult a
    -- Yes n x: consumed n arguments, continue parsing with x
  = Yes Int (ParParser a)
    -- No x: didn't understand this flag, continue parsing with x
  | No (ParParser a)
    -- Error
  | Error String

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
    | otherwise = error "Options.ParseResult: inconsistent number of arguments (internal error)"
  Error s <*> _ = Error s
  _ <*> Error s = Error s
  Yes n r <*> No x = Yes n (r <*> x)
  No x <*> Yes n r = Yes n (x <*> r)
  No f <*> No x = No (f <*> x)

runPar :: ParParser a -> [String] -> Either String (IO a)
runPar p [] = Right (val p)
runPar p xs@(x:_) =
  case peek p xs of
    Yes n p' -> runPar p' (drop n xs)
    No _ -> Left ("Didn't recognise option " ++ x)
    Error err -> Left err

awaitP :: (String -> Bool) -> a -> (String -> [String] -> ParseResult a) -> ParParser a
awaitP p def par = ParParser (return def) f
  where f (x:xs) | p x =
          case par x xs of
            Yes n r -> Yes (n+1) r
            No _ ->
              error "Options.await: got No (internal error)"
            Error err -> Error err
        f _ = No (awaitP p def par)

await :: String -> a -> ([String] -> ParseResult a) -> ParParser a
await flag def f = awaitP (\x -> "--" ++ flag == x) def (const f)

data Flag = Flag
  { flagName :: String,
    flagGroup :: String,
    flagHelp :: [String],
    flagArgs :: String } deriving Show

-- From a flag name and and argument parser, produce an OptionParser.
flag :: String -> [String] -> a -> ArgParser a -> OptionParser a
flag name help def (Annotated desc (SeqParser args f)) =
  Annotated [desc'] (await name def g)
  where desc' = Flag name "Common options" help desc
        g xs =
          case f xs of
            Left err -> Error ("Error in option --" ++ name ++ ": " ++ err)
            Right y -> Yes args (pure y <* noFlag)
        -- Give an error if the flag is repeated.
        noFlag =
          await name ()
            (const (Error ("Option --" ++ name ++ " occurred twice")))

-- Read filenames from the command line.
filenames :: OptionParser [String]
filenames = Annotated [] (from [])
  where from xs = awaitP p xs (f xs)
        p x = not ("--" `isPrefixOf` x)
        f xs y ys = Yes 1 (from (xs ++ [y]))

-- Take a value from the environment.
io :: IO a -> OptionParser a
io m = Annotated [] p
  where p = ParParser m (const (No p))

-- A boolean flag.
bool :: String -> [String] -> OptionParser Bool
bool name help = flag name help False (pure True)

inGroup :: String -> OptionParser a -> OptionParser a
inGroup x (Annotated fls f) = Annotated [fl{ flagGroup = x } | fl <- fls] f

----------------------------------------------------------------------
-- Selecting a particular tool.

type ToolParser = Annotated [Tool] PrefixParser
data Tool = Tool
  { toolName :: String,
    toolVersion :: String,
    toolHelp :: String }

toolProgName :: Tool -> String
toolProgName = small . toolName
  where small (c:cs) = toLower c:cs
        small [] = []

newtype PrefixParser a = PrefixParser (String -> Maybe (ParParser a))

instance Functor PrefixParser where
  fmap f (PrefixParser g) = PrefixParser (fmap (fmap f) . g)

instance Monoid (PrefixParser a) where
  mempty = PrefixParser (const Nothing)
  PrefixParser f `mappend` PrefixParser g =
    PrefixParser (\xs -> f xs `mplus` g xs)

runPref :: PrefixParser a -> [String] -> Either String (IO a)
runPref _ [] = Left "Expected a tool name"
runPref (PrefixParser f) (x:xs) =
  case f x of
    Nothing -> Left ("No such tool " ++ x)
    Just p -> runPar p xs

tool :: Tool -> OptionParser a -> ToolParser a
tool t p =
  Annotated [t] (PrefixParser f)
  where f x | x == toolProgName t = Just (parser p <* helpParser)
        f _ = Nothing
        helpParser =
          await "help" ()
            (const (Yes 0 (parser (io (printHelp (help t p))))))

-- Use the program name as a tool name if possible.
getEffectiveArgs :: ToolParser a -> IO [String]
getEffectiveArgs (Annotated tools _) = do
  progName <- getProgName
  args <- getArgs
  if progName `elem` map toolProgName tools
    then return (progName:args)
    else return args

parseCommandLine :: Tool -> ToolParser a -> IO a
parseCommandLine t p = do
  let p' = p `mappend` toolsHelp t p
  args <- getEffectiveArgs p'
  case runPref (parser p') args of
    Left err -> printHelp (argError t err)
    Right x -> x

----------------------------------------------------------------------
-- Help screens.

printHelp :: [String] -> IO a
printHelp xs = do
  mapM_ putStrLn xs
  exitWith (ExitFailure 1)

argError :: Tool -> String -> [String]
argError t err = [
  greeting t,
  "Error in arguments:",
  err,
  "Try --help."
  ]

toolsHelp :: Tool -> ToolParser a -> ToolParser a
toolsHelp t0 p = tool (Tool "--help" "--help" "0") p'
  where help = concat [
          [greeting t0],
          usage t0 "<toolname> ",
          ["<toolname> can be any of the following:"],
          concat [ justify (toolProgName t) [toolHelp t] | t <- descr p ]
          ]
        help' = [
          greeting t0,
          "Error in arguments:",
          "Didn't expect any arguments after --help.",
          "Try " ++ toolProgName t0 ++ " <toolname> --help if you want help for a particular tool."
          ]
        p' = Annotated [] (ParParser (printHelp help) (const (Yes 1 notEmpty)))
        notEmpty = parser (io (printHelp help'))

help :: Tool -> OptionParser a -> [String]
help t p = concat [
  [greeting t],
  usage t "",
  ["<option> can be any of the following:"],
  concat [ justify ("--" ++ flagName f ++ " " ++ flagArgs f) (flagHelp f) | f <- descr p ]
  ]

greeting :: Tool -> String
greeting t = toolName t ++ ", version " ++ toolVersion t ++ ", 2011-10-04."

usage :: Tool -> String -> [String]
usage t opts = [
  "Usage: " ++ toolProgName t ++ " " ++ opts ++ "<option>* <file>*",
  "",
  "<file> should be in TPTP format.",
  ""
  ]

justify :: String -> [String] -> [String]
justify name help = ["", "  " ++ name] ++ map ("    " ++) help
