{-# LANGUAGE TypeOperators, GADTs #-}
module InferTypes where

import Control.Monad
import Form
import Name
import qualified NameMap
import NameMap(NameMap)
import UnionFind hiding (rep)

type Function' = Name ::: ([Name], Name)
type Variable' = Name ::: Name

inferTypes :: [Input Clause] -> NameM ([Input Clause], Type -> Type)
inferTypes prob = do
  funMap <-
    fmap NameMap.fromList . sequence $
      [ do res <- newName (typ f)
           args <- mapM newName (funArgs f)
           return (name f ::: (args, res))
      | f <- functions prob ]
  varMap <-
    fmap NameMap.fromList . sequence $
      [ do ty <- newName (typ v)
           return (name v ::: ty)
      | v <- vars prob ]
  return (solve funMap varMap prob)

solve :: NameMap Function' -> NameMap Variable' ->
         [Input Clause] -> ([Input Clause], Type -> Type)
solve funMap varMap prob = (prob', typeRep_)
  where prob' = share (aux prob)
        aux :: Symbolic a => a -> a
        aux x =
          case (typeRep x, x, unpack x) of
            (BindRep, Bind vs t, _) ->
              Bind (fmap var vs) (aux t)
            (TermRep, _, _) -> term x
            (_, _, Const x) -> x
            (_, _, Unary f x) -> f (aux x)
            (_, _, Binary f x y) -> f (aux x) (aux y)

        term (f :@: ts) = fun f :@: map term ts
        term (Var x) = Var (var x)

        fun (f ::: _) =
          let (args, res) = rhs (NameMap.lookup_ f funMap)
          in f ::: FunType (map type_ args) (type_ res)

        var (x ::: _) = x ::: type_ (rhs (NameMap.lookup_ x varMap))

        type_ name | name == nameO = O
                   | otherwise = Type (rep name) Infinite Infinite

        rep = evalUF initial $ do
          generate funMap varMap prob
          reps

        typeRep_ t = NameMap.lookup_ (rep (name t)) typeMap
        typeMap = NameMap.fromList (types prob')

generate :: NameMap Function' -> NameMap Variable' -> [Input Clause] -> UF Name ()
generate funMap varMap cs = mapM_ (mapM_ atomic) lss
  where lss = map (map the . toLiterals . what) cs
        atomic (Tru p) = void (term p)
        atomic (t :=: u) = do { t' <- term t; u' <- term u; t' =:= u'; return () }
        term (Var x) = return y
          where _ ::: y = NameMap.lookup_ x varMap
        term (f :@: xs) = do
          ys <- mapM term xs
          let _ ::: (zs, r) = NameMap.lookup_ f funMap
          zipWithM_ (=:=) ys zs
          return r
