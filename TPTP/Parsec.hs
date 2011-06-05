{-# LANGUAGE RankNTypes, BangPatterns, MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, UndecidableInstances #-}
module TPTP.Parsec where

import Control.Applicative
import Control.Monad
import Data.List
import AppList(AppList)
import qualified AppList

-- Parser type and monad instances

newtype Parsec a b = Parsec
  { runParsec :: forall c.
                 a                                       -- Current input
              -> AppList Error                           -- Error message to report on failure
              -> (a -> AppList Error -> b -> Result a c) -- ok: success, nothing consumed
              -> (a -> AppList Error -> b -> Result a c) -- yum: success, something consumed
              -> (a -> AppList Error -> Result a c)      -- err: failure, nothing consumed
              -> Result a c }
  
data Error = Message String | Expected String deriving Show
data Result a b = Ok !a !b | Error !a (AppList Error)

{-# INLINE parseError #-}
parseError :: Error -> Parsec a b
parseError e = Parsec (\inp msg _ _ err -> err inp (AppList.append msg (AppList.Unit e)))

instance Functor (Parsec a) where
  {-# INLINE fmap #-}
  fmap f x = x >>= return . f

instance Monad (Parsec a) where
  {-# INLINE return #-}
  return x = Parsec (\inp msg ok _ _ -> ok inp msg x)
  {-# INLINE (>>=) #-}
  x >>= f = Parsec (\inp msg ok yum err ->
                     let ok' inp' msg' y = runParsec (f y) inp' msg' ok yum err
                         yum' inp msg' y = runParsec (f y) inp msg' yum yum Error
                     in runParsec x inp msg ok' yum' err)
  {-# INLINE fail #-}
  fail msg = parseError (Message msg)

instance MonadPlus (Parsec a) where
  {-# INLINE mzero #-}
  mzero = Parsec (\inp msg ok yum err -> err inp msg)
  {-# INLINE mplus #-}
  m1 `mplus` m2 = Parsec (\inp msg ok yum err ->
    let {-# INLINE err' #-}
        err' _ msg' = runParsec m2 inp msg' ok yum err in
    runParsec m1 inp msg ok yum err')

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
nonempty p = Parsec (\inp msg ok yum err -> runParsec p inp msg (error "nonempty: empty parser") yum err)

{-# INLINE skipSome #-}
skipSome :: Parsec a b -> Parsec a ()
skipSome p = p' where p' = nonempty p >> (p' `mplus` return ())

{-# INLINE skipMany #-}
skipMany :: Parsec a b -> Parsec a ()
skipMany p = p' where p' = (nonempty p >> p') `mplus` return ()

{-# INLINE (<?>) #-}
infix 0 <?>
(<?>) :: Parsec a b -> String -> Parsec a b
p <?> text = Parsec (\inp msg ok yum err ->
  let {-# INLINE add #-}
      add c inp msg' = c inp (AppList.append msg (AppList.Unit (Expected text))) in
  runParsec p inp msg (add ok) yum (add err))

{-# INLINE between #-}
between :: Parsec a b -> Parsec a c -> Parsec a d -> Parsec a d
between p q r = p *> r <* q

{-# INLINE sepBy1 #-}
sepBy1 :: Parsec a b -> Parsec a c -> Parsec a [b]
sepBy1 it sep = liftM2 (:) it (many (sep >> it))

-- Running the parser

{-# INLINE run_ #-}
run_ :: Parsec a b -> a -> Result a b
run_ p x = runParsec p x AppList.Nil (\x _ -> Ok x) (\x _ -> Ok x) Error

{-# INLINE run #-}
run :: Parsec a b -> a -> (a, Either [String] b)
run p ts =
  case run_ p ts of
    Ok ts' x -> (ts', Right x)
    Error ts' e -> (ts', Left (errorMessage e))

-- Reporting errors

errorMessage :: AppList Error -> [String]
errorMessage AppList.Nil = ["Unknown error"]
errorMessage l =
  [ "Expected " ++ list expected | not (null expected) && null messages ]
  ++ messages
  where xs = AppList.toList l
        expected = [ msg | Expected msg <- xs ]
        messages = [ msg | Message msg <- xs ]
        list [msg] = msg
        list msg = intercalate ", " (init msg) ++ " or " ++ last msg

-- Token streams

class Stream a b | a -> b where
  {-# INLINE primToken #-}
  primToken :: a -> (a -> b -> c) -> (AppList Error -> c) -> c
  {-# INLINE primEof #-}
  primEof :: a -> Bool

{-# INLINE satisfy #-}
satisfy :: Stream a b => (b -> Bool) -> Parsec a b
satisfy p = Parsec (\inp msg ok yum err ->
  let ok' inp' t | p t = yum inp' AppList.Nil t
                 | otherwise = err inp msg
  in primToken inp ok' (err inp . AppList.append msg))

{-# INLINE eof #-}
eof :: Stream a b => Parsec a ()
eof = Parsec (\inp msg ok yum err -> if primEof inp then ok inp msg () else err inp msg) <?> "end of file"

-- User state

data UserState state stream = UserState { userState :: !state, userStream :: !stream }

instance Stream a b => Stream (UserState state a) b where
  primToken (UserState state stream) ok err =
    primToken stream (ok . UserState state) err
  primEof = primEof . userStream

{-# INLINE getState #-}
getState :: Parsec (UserState state a) state
getState = Parsec (\inp@UserState{userState = state} msg ok yum err -> ok inp msg state)

{-# INLINE putState #-}
putState :: state -> Parsec (UserState state a) ()
putState state = Parsec (\inp@UserState{userStream = stream} msg ok yum err -> ok (UserState state stream) msg ())
