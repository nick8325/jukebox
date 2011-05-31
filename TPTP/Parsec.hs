{-# LANGUAGE Rank2Types, BangPatterns #-}
-- newtype Parser a b = Parser
--   { runParser :: a -> Result a b }
-- data Result a b = OK b | Fail String | More (Parser a b)
module Parsec(test) where
import Control.Monad
import GHC.Exts

newtype Parser a b = Parser
  { runParser :: forall c.
      a -> (b -> Result a c) -- ok: no input consumed
        -> (a -> b -> Result a c) -- yum: input consumed
        -> (Error -> Result a c) -- err: failed without consuming input
        -> Result a c }

data Error = Base String | App Error Error

data Result a b = Ok !b | Error !a {- input consumed so far -} Error

instance Monad (Parser a) where
  {-# INLINE return #-}
  return x = Parser (\_ ok _ _ -> ok x)
  {-# INLINE (>>=) #-}
  x >>= f = Parser (\inp ok yum err ->
    let ok' y = runParser (f y) inp ok yum err
        yum' inp' y = runParser (f y) inp' (yum inp') yum (Error inp')
    in runParser x inp ok' yum' err)
  {-# INLINE fail #-}
  fail s = Parser (\_ _ _ err -> err (Base s))

instance MonadPlus (Parser a) where
  {-# INLINE mzero #-}
  mzero = fail "mzero"
  {-# INLINE mplus #-}
  m1 `mplus` m2 = Parser (\inp ok yum err ->
    let {-# INLINE err' #-}
        err' s = runParser m2 inp ok yum (err'' s)
        {-# INLINE err'' #-}
        err'' s s2 = err (App s s2)
    in runParser m1 inp ok yum err')

run :: Parser a b -> a -> Result a b
run p x = runParser p x Ok (const Ok) (Error x)

satisfy :: (Int -> Bool) -> Parser IntList Int
satisfy p = Parser (\inp ok yum err ->
  case inp of
    Nil -> err (Base "end of file")
    Cons x xs | p x -> yum xs x
              | otherwise -> err (Base "not satisfying p"))

data IntList = Nil | Cons {-# UNPACK #-} !Int !IntList

-- test = (satisfy (== 42) >> satisfy (== 4)) `mplus` satisfy (== 5) `mplus` (many (satisfy (== 6)) >> return 83)
test = skipMany1 (satisfy (== 83)) `mplus` skipMany1 (satisfy (== 84))
nonempty :: Parser a b -> Parser a b
nonempty p = Parser (\inp ok yum err -> runParser p inp (\_ -> error "ok") yum err)
{-# INLINE skipMany1 #-}
skipMany1 p = nonempty p >> skipMany p
skipMany p = p' where p' = (nonempty p >> p') `mplus` return ()
many p = liftM reverse (p' [])
  where p' !xs = do { x <- nonempty p; p' (x:xs) } `mplus` return xs
