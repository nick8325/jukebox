{-# LANGUAGE ScopedTypeVariables #-}
module TPTP.ParseProblem where

import ProgressBar
import TPTP.FindFile
import TPTP.ClauseParser
import TPTP.Lexer hiding (Include, Error)
import TPTP.Parsec
import TPTP.Print
import qualified TPTP.Lexer as L
import Control.Monad.Error
import Form hiding (Pos)
import qualified Data.ByteString.Lazy.Char8 as BSL
import qualified Data.ByteString.Char8 as BS
import Control.Monad.Identity
import Control.Exception
import Prelude hiding (catch)
import Data.List
import Name

parseProblem :: [FilePath] -> FilePath -> IO (Either String (Problem Form))
parseProblem dirs name = withProgressBar $ \pb -> parseProblemWith (findFileTPTP dirs) pb name

parseProblemWith :: (FilePath -> IO (Maybe FilePath)) -> ProgressBar -> FilePath -> IO (Either String (Problem Form))
parseProblemWith findFile progressBar name = runErrorT (fmap finalise (parseFile name Nothing "<command line>" (Pos 0 0) initialState))
  where err file (Pos l c) msg = throwError msg'
          where msg' = "Error at " ++ file ++ " (line " ++ show l ++ ", column " ++ show c ++ "):\n" ++ msg
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
        parseFile name clauses file0 pos st = do
          file <- liftMaybeIO (findFile name) file0 pos ("File " ++ name ++ " not found")
          liftIO $ enter progressBar $ "Reading " ++ file
          contents <- liftEitherIO
                        (fmap Right (BSL.readFile file >>= tickOnRead progressBar)
                          `catch` (\(e :: IOException) -> return (Left e)))
                        file (Pos 0 0) show
          let s = UserState st (scan contents)
          fmap userState (parseSections clauses file s)

        parseSections :: Maybe [Tag] -> FilePath -> ParsecState -> ErrorT String IO ParsecState
        parseSections clauses file s =
          let report UserState{userStream = At _ Nil} =
                ["Unexpected end of file"]
              report UserState{userStream = At _ L.Error} =
                ["Lexical error"]
              report UserState{userStream = At _ (Cons t _)} =
                ["Unexpected " ++ show t] in
          case run report (section (included clauses)) s of
            (UserState{userStream=At pos _}, Left e) ->
              err file pos (concat (intersperse "\n" e))
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

        finalise :: ParseState -> Problem Form
        finalise (MkState p _ _ _ _ _ n) = close_ n (return (reverse p))
