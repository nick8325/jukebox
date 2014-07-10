{-# LANGUAGE TypeOperators, GADTs #-}
module Jukebox.InferTypes where

import Control.Monad
import Jukebox.Form
import Jukebox.Name
import qualified Jukebox.NameMap as NameMap
import Jukebox.NameMap(NameMap)
import Jukebox.UnionFind hiding (rep)

type Function' = Name ::: ([Type'], Type')
type Variable' = Name ::: Type'
type Type' = Name ::: Type

inferTypes :: [Input Clause] -> NameM ([Input Clause], Type -> Type)
inferTypes prob = do
  funMap <-
    fmap NameMap.fromList . sequence $
      [ do res <- newName (typ f)
           args <- mapM newName (funArgs f)
           return (name f :::
                   (zipWith (:::) args (funArgs f),
                    res ::: typ f))
      | f <- functions prob ]
  varMap <-
    fmap NameMap.fromList . sequence $
      [ do ty <- newName (typ v)
           return (name v ::: (ty ::: typ v))
      | v <- vars prob ]
  
  let tyMap = NameMap.fromList $
              concat [ res:args | _ ::: (args, res) <- NameMap.toList funMap ] ++
              [ ty | _ ::: ty <- NameMap.toList varMap ]
  
  let (prob', rep) = solve funMap varMap prob
      rep' ty = rhs (NameMap.lookup_ (rep (name ty)) tyMap)
  
  return (prob', rep')

solve :: NameMap Function' -> NameMap Variable' ->
         [Input Clause] -> ([Input Clause], Name -> Name)
solve funMap varMap prob = (prob', rep)
  where prob' = share (aux prob)
        aux :: Symbolic a => a -> a
        aux t =
          case typeOf t of
            Bind_ -> bind t
            Term -> term t
            _ -> recursively aux t

        bind :: Symbolic a => Bind a -> Bind a
        bind (Bind vs t) = Bind (fmap var vs) (aux t)

        term (f :@: ts) = fun f :@: map term ts
        term (Var x) = Var (var x)

        fun (f ::: _) =
          let (args, res) = rhs (NameMap.lookup_ f funMap)
          in f ::: FunType (map type_ args) (type_ res)

        var (x ::: _) = x ::: type_ (rhs (NameMap.lookup_ x varMap))

        type_ (name ::: _) 
          | name == nameO = O
          | otherwise = Type (rep name) Infinite Infinite

        rep = evalUF initial $ do
          generate funMap varMap prob
          reps

generate :: NameMap Function' -> NameMap Variable' -> [Input Clause] -> UF Name ()
generate funMap varMap cs = mapM_ (mapM_ atomic) lss
  where lss = map (map the . toLiterals . what) cs
        atomic (Tru p) = void (term p)
        atomic (t :=: u) = do { t' <- term t; u' <- term u; t' =:= u'; return () }
        term (Var x) = return y
          where _ ::: (y ::: _) = NameMap.lookup_ x varMap
        term (f :@: xs) = do
          ys <- mapM term xs
          let _ ::: (zs, r) = NameMap.lookup_ f funMap
          zipWithM_ (=:=) ys (map lhs zs)
          return (lhs r)
