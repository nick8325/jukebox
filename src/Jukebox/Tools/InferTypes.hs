{-# LANGUAGE TypeOperators, GADTs, CPP #-}
module Jukebox.Tools.InferTypes where

#include "errors.h"
import Control.Monad
import Jukebox.Form
import Jukebox.Name
import qualified Data.Map.Strict as Map
import Data.Map(Map)
import Jukebox.UnionFind hiding (rep)
import qualified Data.Set as Set
import Data.MemoUgly

type Function' = ([(Name, Type)], (Name, Type))

inferTypes :: [Input Clause] -> NameM ([Input Clause], Type -> Type)
inferTypes prob = do
  funMap <-
    fmap Map.fromList . sequence $
      [ do res <- newName (typ f)
           args <- mapM newName (funArgs f)
           return (name f,
                   (zipWith (,) args (funArgs f),
                    (res, typ f)))
      | f <- functions prob ]
  varMap <-
    fmap Map.fromList . sequence $
      [ do ty <- newName (typ v)
           return (name v, (ty, typ v))
      | v <- vars prob ]
  
  let tyMap = Map.fromList $
              concat [ res:args | (args, res) <- Map.elems funMap ] ++
              [ ty | ty <- Map.elems varMap ]
  
  let (prob', rep) = solve funMap varMap prob
      rep' ty =
        Map.findWithDefault __ (rep (name ty)) tyMap
  
  return (prob', rep')

solve :: Map Name Function' -> Map Name (Name, Type) ->
         [Input Clause] -> ([Input Clause], Name -> Name)
solve funMap varMap prob = (prob', rep)
  where prob' = aux prob
        aux :: Symbolic a => a -> a
        aux t =
          case typeOf t of
            Bind_ -> bind t
            Term -> term t
            _ -> recursively aux t

        bind :: Symbolic a => Bind a -> Bind a
        bind (Bind vs t) = Bind (Set.map var vs) (aux t)

        term (f :@: ts) = fun f :@: map term ts
        term (Var x) = Var (var x)

        fun = memo fun_
        fun_ (f ::: _) =
          let (args, res) = Map.findWithDefault __ f funMap
          in f ::: FunType (map type_ args) (type_ res)

        var = memo var_
        var_ (x ::: _) = x ::: type_ (Map.findWithDefault __ x varMap)

        type_ = memo type__
        type__ (_, O) = O
        type__ (name, _) = Type (rep name)

        rep = evalUF initial $ do
          generate funMap varMap prob
          reps

generate :: Map Name Function' -> Map Name (Name, Type) -> [Input Clause] -> UF Name ()
generate funMap varMap cs = mapM_ (mapM_ atomic) lss
  where lss = map (map the . toLiterals . what) cs
        atomic (Tru p) = void (term p)
        atomic (t :=: u) = do { t' <- term t; u' <- term u; t' =:= u'; return () }
        term (Var x) = return y
          where (y, _) = Map.findWithDefault __ (name x) varMap
        term (f :@: xs) = do
          ys <- mapM term xs
          let (zs, r) = Map.findWithDefault __ (name f) funMap
          zipWithM_ (=:=) ys (map fst zs)
          return (fst r)
