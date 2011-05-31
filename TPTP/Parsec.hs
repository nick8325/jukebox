{-# LANGUAGE RankNTypes, BangPatterns, MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, UndecidableInstances #-}
module TPTP.Parsec where

import Control.Applicative
import Control.Monad
import AppList(AppList)
import qualified AppList

-- Parser type and monad instances

newtype Parsec a b = Parsec
  { runParsec :: forall c. a -> (a -> b -> Result a c)
                             -> (a -> b -> Result a c)
                             -> (a -> AppList Error -> Result a c)
                             -> Result a c }

data Error = Message String | Expected String deriving Show
data Result a b = Ok !a !b | Error !a (AppList Error)

{-# INLINE parseError #-}
parseError :: Error -> Parsec a b
parseError e = Parsec (\inp _ _ err -> err inp (AppList.Unit e))

instance Functor (Parsec a) where
  {-# INLINE fmap #-}
  fmap f x = x >>= return . f

instance Monad (Parsec a) where
  {-# INLINE return #-}
  return x = Parsec (\inp ok _ _ -> ok inp x)
  {-# INLINE (>>=) #-}
  x >>= f = Parsec (\inp ok yum err ->
                     let ok' inp y = runParsec (f y) inp ok yum err
                         yum' inp y = runParsec (f y) inp yum yum err
                     in runParsec x inp ok' yum' err)

instance MonadPlus (Parsec a) where
  {-# INLINE mzero #-}
  mzero = Parsec (\inp ok yum err -> err inp AppList.Nil)
  m1 `mplus` m2 = Parsec (\inp ok yum err ->
    let {-# INLINE err' #-}
        err' _ s = runParsec m2 inp ok yum (\inp s' -> err inp (AppList.append s s')) in
    runParsec m1 inp ok yum err')

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
  -- many p = liftM reverse (p' [])
  --   where p' !xs = do { x <- nonempty p; p' (x:xs) } `mplus` return xs
  many p = p' where p' = liftM2 (:) (nonempty p) p' <|> return []

-- Basic combinators

{-# INLINE nonempty #-}
nonempty :: Parsec a b -> Parsec a b
nonempty p = Parsec (\inp ok yum err -> runParsec p inp (error "nonempty: empty parser") yum err)

{-# INLINE skipSome #-}
skipSome :: Parsec a b -> Parsec a ()
skipSome p = p' where p' = nonempty p >> (p' `mplus` return ())

{-# INLINE skipMany #-}
skipMany :: Parsec a b -> Parsec a ()
skipMany p = p' where p' = (nonempty p >> p') `mplus` return ()

{-# INLINE (<?>) #-}
infix 0 <?>
(<?>) :: Parsec a b -> String -> Parsec a b
p <?> msg = Parsec (\inp ok yum err ->
  runParsec p inp ok yum (\inp _ -> err inp (AppList.Unit (Expected msg))))

{-# INLINE between #-}
between :: Parsec a b -> Parsec a c -> Parsec a d -> Parsec a d
between p q r = p *> r <* q

{-# INLINE sepBy1 #-}
sepBy1 :: Parsec a b -> Parsec a c -> Parsec a [b]
sepBy1 it sep = liftM2 (:) it (many (sep >> it))

-- Running the parser

{-# INLINE run_ #-}
run_ :: Parsec a b -> a -> Result a b
run_ p x = runParsec p x Ok Ok Error

{-# INLINE run #-}
run :: Parsec a b -> a -> (a, Either (AppList Error) b)
run p ts =
  case run_ p ts of
    Ok ts' x -> (ts', Right x)
    Error ts' e -> (ts', Left e)

-- Token streams

class Stream a b | a -> b where
  {-# INLINE primToken #-}
  primToken :: a -> (a -> b -> c) -> (AppList Error -> c) -> c
  {-# INLINE primEof #-}
  primEof :: a -> Bool

{-# INLINE satisfy #-}
satisfy :: Stream a b => (b -> Bool) -> Parsec a b
satisfy p = Parsec (\inp ok yum err ->
  let ok' inp' t | p t = yum inp' t
                 | otherwise = err inp AppList.Nil
  in primToken inp ok' (err inp))

{-# INLINE eof #-}
eof :: Stream a b => Parsec a ()
eof = Parsec (\inp ok yum err -> if primEof inp then ok inp () else err inp AppList.Nil)

-- User state

data UserState state stream = UserState { userState :: !state, userStream :: !stream }

instance Stream a b => Stream (UserState state a) b where
  primToken (UserState state stream) ok err =
    primToken stream (ok . UserState state) err
  primEof = primEof . userStream

{-# INLINE getState #-}
getState :: Parsec (UserState state a) state
getState = Parsec (\inp@UserState{userState = state} ok yum err -> ok inp state)

{-# INLINE putState #-}
putState :: state -> Parsec (UserState state a) ()
putState state = Parsec (\inp@UserState{userStream = stream} ok yum err -> ok (UserState state stream) ())
