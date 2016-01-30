{-# LANGUAGE RankNTypes, BangPatterns, MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, UndecidableInstances, TypeFamilies #-}
{-# OPTIONS_GHC -funfolding-creation-threshold=10000 -funfolding-use-threshold=10000 #-}
module Jukebox.TPTP.Parsec where

import Control.Applicative
import Control.Monad
import Data.List

-- Parser type and monad instances

newtype Parsec a b = Parsec
  { runParsec :: forall c.
                 (b -> Reply a c -> a -> Reply a c) -- ok: success
              -> Reply a c -- err: backtracking failure
              -> a -> Reply a c }

type Reply a b = [String] -> Result (Position a) b

data Result a b = Ok a b | Error a String | Expected a [String]

{-# INLINE parseError #-}
parseError :: [String] -> Parsec a b
parseError e = Parsec (\_ok err _inp exp -> err (e ++ exp))

{-# INLINE fatalError #-}
fatalError :: Stream a c => String -> Parsec a b
fatalError e = Parsec (\_ok _err inp _ -> Error (position inp) e)

instance Functor (Parsec a) where
  {-# INLINE fmap #-}
  fmap f x = x >>= return . f

instance Monad (Parsec a) where
  {-# INLINE return #-}
  return x = Parsec (\ok err inp exp -> ok x err inp exp)
  {-# INLINE (>>=) #-}
  x >>= f = Parsec (\ok err inp exp  -> runParsec x (\y err inp exp -> runParsec (f y) ok err inp exp) err inp exp)
  {-# INLINE fail #-}
  fail _ = parseError []

instance MonadPlus (Parsec a) where
  {-# INLINE mzero #-}
  mzero = Parsec (\_ok err _inp exp -> err exp)
  {-# INLINE mplus #-}
  m1 `mplus` m2 = Parsec (\ok err inp exp ->
    runParsec m1 ok (\exp -> runParsec m2 ok err inp exp) inp exp)

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
nonempty p = p

{-# INLINE skipSome #-}
skipSome :: Parsec a b -> Parsec a ()
skipSome p = p' where p' = nonempty p >> (p' `mplus` return ())

{-# INLINE skipMany #-}
skipMany :: Parsec a b -> Parsec a ()
skipMany p = p' where p' = (nonempty p >> p') `mplus` return ()

{-# INLINE (<?>) #-}
infix 0 <?>
(<?>) :: Parsec a b -> String -> Parsec a b
p <?> text = Parsec (\ok err inp exp ->
  runParsec p ok err inp (text:exp))

{-# INLINE between #-}
between :: Parsec a b -> Parsec a c -> Parsec a d -> Parsec a d
between p q r = p *> r <* q

{-# INLINE sepBy1 #-}
sepBy1 :: Parsec a b -> Parsec a c -> Parsec a [b]
sepBy1 it sep = liftM2 (:) it (many (sep >> it))

-- Running the parser

run_ :: Stream a c => Parsec a b -> a -> Result (Position a) b
run_ p x = runParsec p ok err x []
  where ok x _ inp _ = Ok (position inp) x
        err exp = Expected (position x) (reverse exp)

run :: Stream a c => (Position a -> [String]) -> Parsec a b -> a -> (Position a, Either [String] b)
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
  type Position a
  position :: a -> Position a

{-# INLINE next #-}
next :: Stream a b => Parsec a b
next = Parsec (\ok err inp exp ->
  primToken inp (\inp' x -> ok x err inp' exp) (err exp) (Error (position inp)))

{-# INLINE cut #-}
cut :: Stream a b => Parsec a ()
cut = Parsec (\ok _err inp _exp -> ok () (Expected (position inp)) inp [])

{-# INLINE cut' #-}
cut' :: Stream a b => Parsec a c -> Parsec a c
cut' p = Parsec (\ok err inp exp -> runParsec p (\x _ inp' _ -> ok x err inp' []) err inp exp)

{-# INLINE satisfy #-}
satisfy :: Stream a b => (b -> Bool) -> Parsec a b
satisfy p = do
  t <- next
  guard (p t)
  cut
  return t

{-# INLINE eof #-}
eof :: Stream a b => Parsec a ()
eof = Parsec (\ok err inp exp ->
  primToken inp (\_ _ -> err ("end of file":exp)) (ok () err inp exp) (Error (position inp)))

-- User state

data UserState state stream = UserState { userState :: !state, userStream :: !stream }

instance Stream a b => Stream (UserState state a) b where
  {-# INLINE primToken #-}
  primToken (UserState state stream) ok err =
    primToken stream (ok . UserState state) err
  type Position (UserState state a) = UserState state a
  position = id

{-# INLINE getState #-}
getState :: Parsec (UserState state a) state
getState = Parsec (\ok err inp@UserState{userState = state} exp -> ok state err inp exp)

{-# INLINE putState #-}
putState :: state -> Parsec (UserState state a) ()
putState state = Parsec (\ok err UserState{userStream = stream} exp -> ok () err (UserState state stream) exp)
