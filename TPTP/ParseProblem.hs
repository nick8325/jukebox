{-# LANGUAGE ScopedTypeVariables #-}
module TPTP.ParseProblem where

import ProgressBar
import TPTP.FindFile
import TPTP.ClauseParser
import TPTP.Lexer hiding (Include, Error)
import TPTP.Parsec
import qualified TPTP.Lexer as L
import Control.Monad.Error
import Formula hiding (Pos)
import qualified Data.ByteString.Lazy.Char8 as BSL
import qualified Data.ByteString.Char8 as BS
import Control.Monad.Identity
import qualified Data.Map as Map
import Control.Exception
import Prelude hiding (catch)
import Data.List

parseProblem :: FilePath -> IO (Either String (Problem Formula))
parseProblem name = withProgressBar $ \pb -> parseProblemWith (findFileTPTP []) pb name

parseProblemWith :: (FilePath -> IO (Maybe FilePath)) -> ProgressBar -> FilePath -> IO (Either String (Problem Formula))
parseProblemWith findFile progressBar name = runErrorT (fmap finalise (parseFile name Nothing "<command line>" (Pos 0 0) initialState))
  where err file pos msg = throwError (file ++ "/" ++ show pos ++ "/" ++ show msg)
        liftMaybeIO :: IO (Maybe a) -> FilePath -> Pos -> String -> ErrorT String IO a
        liftMaybeIO m file pos msg = do
          x <- liftIO m
          case x of
            Nothing -> err file pos msg
            Just x -> return x
        liftEitherIO :: IO (Either a b) -> FilePath -> Pos -> (a -> String) -> ErrorT String IO b
        liftEitherIO m file pos msg = do
          x <- liftIO m
          case x of
            Left e -> err file pos (msg e)
            Right x -> return x

        parseFile :: FilePath -> Maybe [Tag] -> FilePath -> Pos ->
                     ParseState -> ErrorT FilePath IO ParseState
        parseFile name clauses file0 pos (MkState prob ind) = do
          file <- liftMaybeIO (findFile name) file0 pos ("File " ++ name ++ " not found")
          liftIO $ enter progressBar $ "Reading " ++ file
          contents <- liftEitherIO
                        (fmap Right (BSL.readFile file >>= tickOnRead progressBar)
                          `catch` (\(e :: IOException) -> return (Left e)))
                        file (Pos 0 0) show
          let s = UserState (MkState prob ind) (scan contents)
          fmap userState (parseSections clauses file s)

        parseSections :: Maybe [Tag] -> FilePath -> ParsecState -> ErrorT String IO ParsecState
        parseSections clauses file s =
          case run (section (included clauses)) s of
            (UserState{userStream=At pos _}, Left e) -> err file pos e
            (s'@UserState{userStream=At _ Nil}, Right Nothing) -> do
              liftIO $ leave progressBar
              return s'
            (UserState{userStream=stream@(At pos _),userState=state},
             Right (Just (Include name clauses'))) -> do
              s' <- parseFile (BS.unpack name) (clauses `merge` clauses') file pos state
              parseSections clauses file (UserState s' stream)

        included :: Maybe [Tag] -> Tag -> Bool
        included Nothing _ = True
        included (Just xs) x = x `elem` xs

        merge :: Maybe [Tag] -> Maybe [Tag] -> Maybe [Tag]
        merge Nothing x = x
        merge x Nothing = x
        merge (Just xs) (Just ys) = Just (xs `intersect` ys)

        finalise :: ParseState -> Problem Formula
        finalise (MkState p _) = p { inputs = reverse (inputs p) }
