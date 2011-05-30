{-# LANGUAGE ScopedTypeVariables #-}
module TPTP.ParseProblem where

import Text.Parsec(ParseError)

import ProgressBar
import TPTP.FindFile
import TPTP.ClauseParser
import TPTP.Lexer hiding (Include, Error)
import qualified TPTP.Lexer as L
import Control.Monad.Error
import Formula hiding (Pos)
import Text.Parsec hiding (runParser)
import Text.Parsec.Error
import Text.Parsec.Pos
import qualified Data.ByteString.Lazy.Char8 as BSL
import qualified Data.ByteString.Char8 as BS
import Control.Monad.Identity
import qualified Data.Map as Map
import Control.Exception
import Prelude hiding (catch)
import Data.List

parseProblem :: FilePath -> IO (Either ParseError (Problem Formula))
parseProblem name = withProgressBar $ \pb -> parseProblemWith (findFileTPTP []) pb name

-- The I/O part of the parser loop, which has the job of handling
-- include files, finding and reading files and updating the progress bar.
-- This is a bit icky.
instance Error ParseError where
  noMsg = strMsg "unknown error"
  strMsg msg = newErrorMessage (Message msg) (newPos "<unknown>" 0 0)

parseProblemWith :: (FilePath -> IO (Maybe FilePath)) -> ProgressBar -> FilePath -> IO (Either ParseError (Problem Formula))
parseProblemWith findFile progressBar name = runErrorT (fmap finalise (parseFile name Nothing pos0 initialState))
  where pos0 = newPos "<command line>" 0 0

        err pos msg = throwError (newErrorMessage (Message msg) pos)
        liftMaybeIO :: IO (Maybe a) -> SourcePos -> String -> ErrorT ParseError IO a
        liftMaybeIO m pos msg = do
          x <- liftIO m
          case x of
            Nothing -> err pos msg
            Just x -> return x
        liftEitherIO :: IO (Either a b) -> SourcePos -> (a -> String) -> ErrorT ParseError IO b
        liftEitherIO m pos msg = do
          x <- liftIO m
          case x of
            Left e -> err pos (msg e)
            Right x -> return x

        parseFile :: FilePath -> Maybe [Tag] -> SourcePos ->
                     ParseState -> ErrorT ParseError IO ParseState
        parseFile name clauses pos (MkState prob ind) = do
          file <- liftMaybeIO (findFile name) pos ("File " ++ name ++ " not found")
          liftIO $ enter progressBar $ "Reading " ++ file
          contents <- liftEitherIO
                        (fmap Right (BSL.readFile file >>= tickOnRead progressBar)
                          `catch` (\(e :: IOException) -> return (Left e)))
                        (newPos file 0 0) show
          let s = openFile file (scan contents) (MkState prob ind)
          fmap stateUser (parseSections clauses s)

        parseSections :: Maybe [Tag] -> ParsecState -> ErrorT ParseError IO ParsecState
        parseSections clauses s =
          case runParser (section (included clauses)) s of
            Left e -> throwError e
            Right (Nothing, s'@State{stateInput = Nil}) -> do
              liftIO $ leave progressBar
              return s'
            Right (Just (Include name clauses'), State tokens pos s) -> do
              s' <- parseFile (BS.unpack name) (clauses `merge` clauses') pos s
              parseSections clauses (State tokens pos s')

        included :: Maybe [Tag] -> Tag -> Bool
        included Nothing _ = True
        included (Just xs) x = x `elem` xs

        merge :: Maybe [Tag] -> Maybe [Tag] -> Maybe [Tag]
        merge Nothing x = x
        merge x Nothing = x
        merge (Just xs) (Just ys) = Just (xs `intersect` ys)

        finalise :: ParseState -> Problem Formula
        finalise (MkState p _) = p { inputs = reverse (inputs p) }
