{-# LANGUAGE FlexibleContexts #-}
module Options where

import Control.Arrow((***))
import Control.Applicative
import Control.Monad(mplus)
import Data.Char
import Data.List
import Data.Monoid
import System.Environment
import System.Exit
import System.IO

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
    consume :: [String] -> Either Error a }

instance Functor SeqParser where
  fmap f (SeqParser a c) = SeqParser a (fmap f . c)

instance Applicative SeqParser where
  pure = SeqParser 0 . const . pure
  SeqParser a c <*> SeqParser a' c' = SeqParser (a + a') f
    where f xs = c xs <*> c' (drop a xs)

arg :: ArgDesc -> String -> (String -> Maybe a) -> ArgParser a
arg desc err f = Annotated desc (SeqParser 1 c)
  where c [] = Left (Mistake err)
        c (x:_) | "--" `isPrefixOf` x = Left (Mistake err)
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

-- A parser that always fails but produces an error message (useful for --help etc.)
argUsage :: ExitCode -> [String] -> ArgParser a
argUsage code err = Annotated [] (SeqParser 0 (const (Left (Usage code err))))

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

awaitP :: (String -> Bool) -> a -> (String -> [String] -> ParseResult a) -> ParParser a
awaitP p def par = ParParser (return def) f
  where f (x:xs) | p x =
          case par x xs of
            Yes n r -> Yes (n+1) r
            No _ ->
              error "Options.await: got No"
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
            Left (Mistake err) -> Error (Mistake ("Error in option --" ++ name ++ ": " ++ err))
            Left (Usage code err) -> Error (Usage code err)
            Right y -> Yes args (pure y <* noFlag)
        -- Give an error if the flag is repeated.
        noFlag =
          await name ()
            (const (Error (Mistake ("Option --" ++ name ++ " occurred twice"))))

manyFlags :: String -> [String] -> ArgParser a -> OptionParser [a]
manyFlags name help (Annotated desc (SeqParser args f)) =
  fmap reverse (Annotated [desc'] (go []))
  where desc' = Flag name "Common options" help desc
        go xs = await name xs (g xs)
        g xs ys =
          case f ys of
            Left (Mistake err) -> Error (Mistake ("Error in option --" ++ name ++ ": " ++ err))
            Left (Usage code err) -> Error (Usage code err)
            Right x -> Yes args (go (x:xs))

-- Read filenames from the command line.
filenames :: OptionParser [String]
filenames = Annotated [] (from [])
  where from xs = awaitP p xs (f xs)
        p x = not ("--" `isPrefixOf` x)
        f xs y ys = Yes 0 (from (xs ++ [y]))

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
  { toolProgName :: String,
    toolName :: String,
    toolVersion :: String,
    toolHelp :: String }

newtype PrefixParser a = PrefixParser (String -> Maybe (Tool, ParParser a))

instance Functor PrefixParser where
  fmap f (PrefixParser g) = PrefixParser (fmap (id *** fmap f) . g)

instance Monoid (PrefixParser a) where
  mempty = PrefixParser (const Nothing)
  PrefixParser f `mappend` PrefixParser g =
    PrefixParser (\xs -> f xs `mplus` g xs)

runPref :: PrefixParser a -> [String] -> Either Error (IO a)
runPref _ [] = Left (Mistake "Expected a tool name")
runPref (PrefixParser f) (x:xs) =
  case f x of
    Nothing -> Left (Mistake ("No such tool " ++ x))
    Just (t, p) ->
      case runPar p xs of
        Left (Mistake x) -> Left (Usage (ExitFailure 1) (argError t x))
        Left (Usage code x) -> Left (Usage code x)
        Right x -> Right x

tool :: Tool -> OptionParser a -> ToolParser a
tool t p =
  Annotated [t] (PrefixParser f)
  where f x | x == toolProgName t = Just (t, parser p')
        f _ = Nothing
        p' = p <* versionParser <* helpParser
        helpParser = flag "help" ["Show this help text."] () (argUsage ExitSuccess (help t p'))
        versionParser = flag "version" ["Print the version number."] () (argUsage ExitSuccess [greeting t])

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
  let p' = versionTool t `mappend` helpTool t p `mappend` p
  args <- getEffectiveArgs p'
  case runPref (parser p') args of
    Left (Mistake err) -> printHelp (ExitFailure 1) (argError t err)
    Left (Usage code err) -> printHelp code err
    Right x -> x

----------------------------------------------------------------------
-- Help screens.

printHelp :: ExitCode -> [String] -> IO a
printHelp code xs = do
  mapM_ (hPutStrLn stderr ) xs
  exitWith code

argError :: Tool -> String -> [String]
argError t err = [
  greeting t,
  err ++ ". Try --help."
  ]

usageTool :: Tool -> String -> [String] -> String -> ToolParser a
usageTool t0 flag msg bit = tool (Tool flag' flag' flag' "0") p
  where p = Annotated [] (ParParser (printHelp ExitSuccess msg)
                                    (const (Error (Usage (ExitFailure 1) msg'))))
        flag' = "--" ++ flag
        msg' = [
          greeting t0,
          "Didn't expect any arguments after " ++ flag' ++ ".",
          "Try " ++ toolProgName t0 ++ " <toolname> " ++ flag' ++ " if you want " ++ bit ++ " a particular tool."
          ]

versionTool :: Tool -> ToolParser a
versionTool t0 = usageTool t0 "version" [greeting t0] "the version of"

helpTool :: Tool -> ToolParser a -> ToolParser a
helpTool t0 p = usageTool t0 "help" help "help for"
  where help = concat [
          [greeting t0],
          usage t0 "<toolname> ",
          ["<toolname> can be any of the following:"],
          concat [ justify (toolProgName t) [toolHelp t] | t <- descr p ],
          ["", "Use " ++ toolProgName t0 ++ " <toolname> --help for help on a particular tool."]
          ]

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
  toolHelp t ++ ".",
  "",
  "<file> should be in TPTP format.",
  ""
  ]

justify :: String -> [String] -> [String]
justify name help = ["", "  " ++ name] ++ map ("    " ++) help
