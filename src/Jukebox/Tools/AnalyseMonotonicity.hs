{-# LANGUAGE TypeOperators, CPP #-}
module Jukebox.Tools.AnalyseMonotonicity where

import Prelude hiding (lookup)
import Jukebox.Name
import Jukebox.Form hiding (Form, clause, true, false, And, Or)
import Control.Monad
import qualified Data.Map.Strict as Map
import Data.Map(Map)
#ifndef NO_MINISAT
import Jukebox.Sat.Easy
#endif

data Extension = TrueExtend | FalseExtend | CopyExtend deriving Show

data Var = FalseExtended Function | TrueExtended Function deriving (Eq, Ord)

annotateMonotonicity :: Problem Clause -> IO (Problem Clause)
annotateMonotonicity prob = do
  m <- monotone (map what prob)
  let f O = O
      f ty =
        case Map.lookup ty m of
          Nothing -> ty
          Just{} -> ty { tmonotone = Finite 0 }
  return (fmap (mapType f) prob)

monotone :: [Clause] -> IO (Map Type (Maybe (Map Function Extension)))
#ifdef NO_MINISAT
monotone _ = return Map.empty
#else
monotone cs = runSat watch tys $ do
  let fs = functions cs
  mapM_ (clause . toLiterals) cs
  fmap Map.fromList . forM tys $ \ty -> atIndex ty $ do
    r <- solve []
    case r of
      False -> return (ty, Nothing)
      True -> do
        m <- model
        return (ty, Just (fromModel fs ty m))
  where watch (FalseExtended f) =
          addForm (Or [Lit (Neg (FalseExtended f)),
                       Lit (Neg (TrueExtended f))])
        watch _ = return ()
        tys = types' cs

fromModel :: [Function] -> Type -> (Var -> Bool) -> Map Function Extension
fromModel fs ty m = Map.fromList [ (f, extension f m) | f <- fs, typ f == O, ty `elem` args (rhs f) ]

extension :: Function -> (Var -> Bool) -> Extension
extension f m =
  case (m (FalseExtended f), m (TrueExtended f)) of
    (False, False) -> CopyExtend
    (True, False) -> FalseExtend
    (False, True) -> TrueExtend

clause :: [Literal] -> Sat Var Type ()
clause ls = mapM_ (literal ls) ls

literal :: [Literal] -> Literal -> Sat Var Type ()
literal ls (Pos (t :=: u)) = atIndex (typ t) $ do
  addForm (safe ls t)
  addForm (safe ls u)
literal _ls (Neg (_ :=: _)) = return ()
literal ls (Pos (Tru (p :@: ts))) =
  forM_ ts $ \t -> atIndex (typ t) $ addForm (Or [safe ls t, Lit (Neg (FalseExtended p))])
literal ls (Neg (Tru (p :@: ts))) =
  forM_ ts $ \t -> atIndex (typ t) $ addForm (Or [safe ls t, Lit (Neg (TrueExtended p))])

safe :: [Literal] -> Term -> Form Var
safe ls (Var x) = Or [ guards l x | l <- ls ]
safe _ _ = true

guards :: Literal -> Variable -> Form Var
guards (Neg (Var _ :=: Var _)) _ = error "Monotonicity.guards: found a variable inequality X!=Y after clausification"
guards (Neg (Var x :=: _)) y | x == y = true
guards (Neg (_ :=: Var x)) y | x == y = true
guards (Pos (Tru (p :@: ts))) x | Var x `elem` ts = Lit (Pos (TrueExtended p))
guards (Neg (Tru (p :@: ts))) x | Var x `elem` ts = Lit (Pos (FalseExtended p))
guards _ _ = false
#endif
