module Options where

import Control.Applicative
import Control.Monad(mplus)
import Data.Char
import Data.List
import Data.Monoid
import System.Environment

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

data Flag = Flag
  { flagName :: String,
    flagGroup :: String,
    flagHelp :: [String],
    flagArgs :: String } deriving Show

-- From a flag name and and argument parser, produce an OptionParser.
-- This is icky: would be nicer with some pretty combinators.
flag :: String -> [String] -> a -> ArgParser a -> OptionParser a
flag name help def (Annotated desc (SeqParser args f)) =
  Annotated [desc'] (ParParser (return def) g)
  where desc' = Flag name "Common options" help desc
        g (x:xs)
          | x == "--" ++ name =
            case f xs of
              Left err -> Error ("Error in option --" ++ name ++ ": " ++ err)
              Right y -> Yes (args+1) (pure y <* noFlag)
        g _ = No (ParParser (return def) g)
        -- Give an error if the flag is repeated.
        noFlag = ParParser (return ()) f
          where f (x:_) | x == "--" ++ name =
                  Error ("Option --" ++ name ++ " occurred twice")
                f _ = No noFlag

-- Read filenames from the command line.
filenames :: OptionParser [String]
filenames = Annotated [] (from [])
  where from xs = ParParser (return xs) (f xs)
        f xs (y:ys)
          | not ("--" `isPrefixOf` y) = Yes 1 (from (xs ++ [y]))
        f xs _ = No (from xs)

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

type ToolParser = Annotated [(String, String)] PrefixParser

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

tool :: String -> String -> OptionParser a -> ToolParser a
tool name help p =
  Annotated [(name, help)] (PrefixParser f)
  where f x | x == name = Just (parser p)
        f _ = Nothing

-- Use the program name as a tool name if possible.
getEffectiveArgs :: ToolParser a -> IO [String]
getEffectiveArgs (Annotated tools _) = do
  progName <- getProgName
  args <- getArgs
  if progName `elem` map fst tools
    then return (progName:args)
    else return args

parseCommandLine :: ToolParser a -> IO (Either String a)
parseCommandLine p = do
  args <- getEffectiveArgs p
  case runPref (parser p) args of
    Left err -> return (Left err)
    Right x -> fmap Right x
