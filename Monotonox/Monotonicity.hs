{-# LANGUAGE TemplateHaskell, TypeOperators #-}
module Monotonicity where

import Name
import Form hiding (Form, clause, true, false)
import Sat
import NameMap
import Utils
import Data.DeriveTH
import Data.Derive.Hashable
import Data.Hashable
import Control.Monad

data Extension = TrueExtend | FalseExtend | CopyExtend deriving Show

data Var = FalseExtended Function Type | TrueExtended Function Type | AtType Type deriving (Eq, Ord)

$(derive makeHashable ''Var)

monotone :: [Clause] -> IO (NameMap (Type ::: Maybe (NameMap (Function ::: Extension))))
monotone cs = runSat watch $ do
  let fs = functions cs
  mapM_ (clause . toLiterals) cs
  fmap NameMap.fromList . forM (filter (/= O) (types cs)) $ \ty -> do
    r <- solve [Pos (AtType ty)]
    case r of
      False -> return (ty ::: Nothing)
      True -> do
        m <- model
        return (ty ::: Just (fromModel fs ty m))
  where watch (FalseExtended f ty) =
          addForm (disj [Lit (Neg (FalseExtended f ty)),
                         Lit (Neg (TrueExtended f ty))])
        watch _ = return ()

fromModel :: [Function] -> Type -> (Var -> Bool) -> NameMap (Function ::: Extension)
fromModel fs ty m = NameMap.fromList [ f ::: extension f ty m | f <- fs, typ f == O, ty `elem` args (rhs f) ]

extension :: Function -> Type -> (Var -> Bool) -> Extension
extension f ty m =
  case (m (FalseExtended f ty), m (TrueExtended f ty)) of
    (False, False) -> CopyExtend
    (True, False) -> FalseExtend
    (False, True) -> TrueExtend

clause :: [Literal] -> Sat Var ()
clause ls = mapM_ (literal ls) ls

literal :: [Literal] -> Literal -> Sat Var ()
literal ls (Pos (t :=: u)) = do
  addForm (safe ls t)
  addForm (safe ls u)
literal ls (Neg (_ :=: _)) = return ()
literal ls (Pos (Tru (p :@: ts))) =
  forM_ ts $ \t -> addForm (disj [safe ls t, Lit (Neg (FalseExtended p (typ t)))])
literal ls (Neg (Tru (p :@: ts))) =
  forM_ ts $ \t -> addForm (disj [safe ls t, Lit (Neg (TrueExtended p (typ t)))])

safe :: [Literal] -> Term -> Form Var
safe ls (Var x) = disj (Lit (Neg (AtType (typ x))):[ guards l x | l <- ls ])
safe _ _ = true

guards :: Literal -> Variable -> Form Var
guards (Neg (Var _ :=: Var _)) _ = error "Monotonicity.guards: found a variable inequality X!=Y after clausification"
guards (Neg (Var x :=: _)) y | x == y = true
guards (Neg (_ :=: Var x)) y | x == y = true
guards (Pos (Tru (p :@: ts))) x | Var x `elem` ts = Lit (Pos (TrueExtended p (typ x)))
guards (Neg (Tru (p :@: ts))) x | Var x `elem` ts = Lit (Pos (FalseExtended p (typ x)))
guards _ _ = false