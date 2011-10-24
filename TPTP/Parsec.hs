{-# LANGUAGE RankNTypes, BangPatterns, MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, UndecidableInstances #-}
module TPTP.Parsec where

import Control.Applicative
import Control.Monad
import Data.List
import Data.Maybe

-- Parser type and monad instances

newtype Parsec a b = Parsec
  { runParsec :: forall c.
                 a                                  -- Current input
              -> [String]                           -- Expected tokens
              -> (a -> [String] -> b -> Result a c) -- ok: success, nothing consumed
              -> (a -> [String] -> b -> Result a c) -- yum: success, something consumed
              -> (a -> [String] -> Result a c)      -- err: failure, nothing consumed
              -> Result a c }
  
data Result a b = Ok !a !b | Error !a String | Expected !a [String]

{-# INLINE parseError #-}
parseError :: [String] -> Parsec a b
parseError e = Parsec (\inp exp _ _ err -> err inp (e ++ exp))

{-# INLINE fatalError #-}
fatalError :: String -> Parsec a b
fatalError e = Parsec (\inp _ _ _ _ -> Error inp e)

instance Functor (Parsec a) where
  {-# INLINE fmap #-}
  fmap f x = x >>= return . f

instance Monad (Parsec a) where
  {-# INLINE return #-}
  return x = Parsec (\inp exp ok _ _ -> ok inp exp x)
  {-# INLINE (>>=) #-}
  x >>= f = Parsec (\inp exp ok yum err ->
                     let ok' inp' exp' y = runParsec (f y) inp' exp' ok yum err
                         yum' inp exp' y = runParsec (f y) inp exp' yum yum Expected
                     in runParsec x inp exp ok' yum' err)
  {-# INLINE fail #-}
  fail _ = parseError []

instance MonadPlus (Parsec a) where
  {-# INLINE mzero #-}
  mzero = Parsec (\inp exp ok yum err -> err inp exp)
  {-# INLINE mplus #-}
  m1 `mplus` m2 = Parsec (\inp exp ok yum err ->
    let {-# INLINE err' #-}
        err' _ exp' = runParsec m2 inp exp' ok yum err in
    runParsec m1 inp exp ok yum err')

instance Applicative (Parsec a) where
  {-# INLINE pure #-}
  pure = return
  {-# INLINE (<*>) #-}
  f <*> x = do { f' <- f; x' <- x; return (f' x') }
  {-# INLINE (*>) #-}
  (*>) = (>>)
  {-# INLINE (<*) #-}
  x <* y = do
    x' <- x
    y
    return x'

instance Alternative (Parsec a) where
  {-# INLINE empty #-}
  empty = mzero
  {-# INLINE (<|>) #-}
  (<|>) = mplus
  {-# INLINE some #-}
  some p = do { x <- nonempty p; xs <- many p; return (x:xs) }
  {-# INLINE many #-}
  many p = p' where p' = liftM2 (:) (nonempty p) p' <|> return []
  -- Stack overflow-avoiding version:
  -- many p = liftM reverse (p' [])
  --   where p' !xs = do { x <- nonempty p; p' (x:xs) } `mplus` return xs

-- Basic combinators

{-# INLINE nonempty #-}
nonempty :: Parsec a b -> Parsec a b
nonempty p = Parsec (\inp exp ok yum err -> runParsec p inp exp (\inp _ _ -> Error inp "nonempty: empty parser") yum err)

{-# INLINE skipSome #-}
skipSome :: Parsec a b -> Parsec a ()
skipSome p = p' where p' = nonempty p >> (p' `mplus` return ())

{-# INLINE skipMany #-}
skipMany :: Parsec a b -> Parsec a ()
skipMany p = p' where p' = (nonempty p >> p') `mplus` return ()

{-# INLINE (<?>) #-}
infix 0 <?>
(<?>) :: Parsec a b -> String -> Parsec a b
p <?> text = Parsec (\inp exp ok yum err ->
  let {-# INLINE add #-}
      add c inp exp' = c inp (text:exp) in
  runParsec p inp exp (add ok) yum (add err))

{-# INLINE between #-}
between :: Parsec a b -> Parsec a c -> Parsec a d -> Parsec a d
between p q r = p *> r <* q

{-# INLINE sepBy1 #-}
sepBy1 :: Parsec a b -> Parsec a c -> Parsec a [b]
sepBy1 it sep = liftM2 (:) it (many (sep >> it))

-- Running the parser

run_ :: Parsec a b -> a -> Result a b
run_ p x = runParsec p x [] ok ok err
  where ok inp _ = Ok inp
        err inp exp = Expected inp (reverse exp)

run :: (a -> [String]) -> Parsec a b -> a -> (a, Either [String] b)
run report p ts =
  case run_ p ts of
    Ok ts' x -> (ts', Right x)
    Error ts' e -> (ts', Left [e])
    Expected ts' e -> (ts', Left (expected (report ts') e))

-- Reporting errors

expected :: [String] -> [String] -> [String]
expected unexpected [] = unexpected ++ ["Unknown error"]
expected unexpected expected =
  unexpected ++ [ "Expected " ++ list expected ]
  where list [exp] = exp
        list exp = intercalate ", " (init exp) ++ " or " ++ last exp

-- Token streams

class Stream a b | a -> b where
  primToken :: a -> (a -> b -> c) -> c -> (String -> c) -> c

{-# INLINE satisfy #-}
satisfy :: Stream a b => (b -> Bool) -> Parsec a b
satisfy p = Parsec (\inp exp ok yum err ->
  let {-# INLINE ok' #-}
      ok' inp' t | p t = yum inp' [] t
                 | otherwise = err inp exp
  in primToken inp ok' (err inp exp) (Error inp))

{-# INLINE eof #-}
eof :: Stream a b => Parsec a ()
eof = Parsec (\inp exp ok yum err ->
  let {-# INLINE ok' #-}
      ok' _ _ = err inp ("end of file":exp)
  in primToken inp ok' (ok inp exp ()) (Error inp))

-- User state

data UserState state stream = UserState { userState :: !state, userStream :: !stream }

instance Stream a b => Stream (UserState state a) b where
  {-# INLINE primToken #-}
  primToken (UserState state stream) ok err =
    primToken stream (ok . UserState state) err

{-# INLINE getState #-}
getState :: Parsec (UserState state a) state
getState = Parsec (\inp@UserState{userState = state} exp ok yum err -> ok inp exp state)

{-# INLINE putState #-}
putState :: state -> Parsec (UserState state a) ()
putState state = Parsec (\inp@UserState{userStream = stream} exp ok yum err -> ok (UserState state stream) exp ())
