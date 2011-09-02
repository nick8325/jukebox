{-# LANGUAGE ImplicitParams, TupleSections #-}
module InferTypes where

import UnionFind hiding (S)
import Control.Monad.State.Strict
import Formula hiding (funs, preds, types)
import qualified Formula
import qualified Data.HashMap as Map
import Data.HashMap(Map)
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJClass
import TPTP.Print
import Data.Hashable
import qualified Seq as S
import Data.Ord

-- Type names
data InferName = InferName !Name {-# UNPACK #-} !Int
baseName :: InferName -> Name
baseName (InferName name _) = name
label :: InferName -> Int
label (InferName _ x) = x

instance Eq InferName where
  x == y = label x == label y

instance Ord InferName where
  compare = comparing label

instance Hashable InferName where
  hashWithSalt s = hashWithSalt . label

instance Pretty InferName where
  pPrint (InferName x n) = pPrint x <> text "_" <> pPrint n

instance Show InferName where
  show = chattyShow

data S = S {
  funs :: Name -> ([Type InferName], Function InferName),
  preds :: Name -> ([Type InferName], Predicate InferName),
  index :: !Int,
  types :: [Type InferName]
  }

type M = StateT S (UF InferName)

inferTerm :: (?ctx :: Variable Name -> Variable InferName) => Term Name -> M (Term InferName)
inferTerm (Var x) = return (Var (?ctx x))
inferTerm (f :@: xs) = do
  (args, f') <- gets (flip funs (fname f))
  xs' <- mapM inferTerm xs
  lift $ zipWithM_ (=:=) (map tname args) (map (tname . ty) xs')
  return (f' :@: xs')

inferAtom :: (?ctx :: Variable Name -> Variable InferName) => Atom Name -> M (Atom InferName)
inferAtom (t :=: u) = do
  t' <- inferTerm t
  u' <- inferTerm u
  lift $ tname (ty t') =:= tname (ty u')
  return (t' :=: u')
inferAtom (p :?: xs) = do
  (args, p') <- gets (flip preds (pname p))
  xs' <- mapM inferTerm xs
  lift $ zipWithM_ (=:=) (map tname args) (map (tname . ty) xs')
  return (p' :?: xs')

inferFormula :: (?monotone :: Type InferName -> DomainSize, ?size :: Type InferName -> DomainSize) =>
                (Map (Variable Name) (Variable InferName)) ->
                Formula Name -> 
                M (Formula InferName)
inferFormula ctx (Literal l) =
  let ?ctx = \x -> Map.findWithDefault (error "inferFormula: unbound variable") x ctx in
  fmap (Literal . resign (sign l)) (inferAtom (value l))
inferFormula ctx (Not f) = fmap Not (inferFormula ctx f)
inferFormula ctx (And fs) = fmap (And . S.fromList) (mapM (inferFormula ctx) (S.toList fs))
inferFormula ctx (Or fs) = fmap (Or . S.fromList) (mapM (inferFormula ctx) (S.toList fs))
inferFormula ctx (Equiv f g) = liftM2 Equiv (inferFormula ctx f) (inferFormula ctx g)
inferFormula ctx (ForAll xs f) = binder ForAll ctx xs f
inferFormula ctx (Exists xs f) = binder Exists ctx xs f

binder q ctx xs f = do
  let xsl = Set.toList xs
  xs' <- forM xsl $ \x ->
         do { ty <- freshType (vtype x); return (Variable (InferName (vname x) 0) ty) }
  let ctx' = foldr (uncurry Map.insert) ctx (zip xsl xs')
  fmap (q (Set.fromList xs')) (inferFormula ctx' f)

freshType :: (?monotone :: Type InferName -> DomainSize, ?size :: Type InferName -> DomainSize) =>
             Type Name -> M (Type InferName)
freshType (Type name _ _ cls) = do
  s <- get
  let ty = Type (InferName name (index s)) (?monotone ty) (?size ty) cls
  put s { index = index s + 1, types = ty:types s }
  return ty

inferInput :: (?monotone :: Type InferName -> DomainSize, ?size :: Type InferName -> DomainSize) =>
              Input (Formula Name) -> M (Input (Formula InferName))
inferInput (Input tag kind form) = fmap (Input tag kind) (inferFormula Map.empty form)

inferProblem :: (?monotone :: Type InferName -> DomainSize, ?size :: Type InferName -> DomainSize) =>
                Problem Formula Name -> M (Problem Formula InferName)
inferProblem (Problem _ preds funs inputs) = do
  let freshPred (name, (args, p)) = do
        args' <- mapM freshType args
        let name' = InferName name 0
        return (name', (args', Predicate name'))
  let freshFun (name, (args, f)) = do
        args' <- mapM freshType args
        res' <- freshType (fres f)
        let name' = InferName name 0
        return (name', (args', Function name' res'))
  preds' <- fmap Map.fromList . mapM freshPred . toListH $ preds
  funs' <- fmap Map.fromList . mapM freshFun . toListH $ funs
  s <- get
  put s { preds = \x -> Map.findWithDefault (error "inferProblem: predicate not found") (InferName x 0) preds',
          funs = \x -> Map.findWithDefault (error "inferProblem: function not found") (InferName x 0) funs' }
  inputs' <- mapM inferInput inputs
  let toMap xs = Map.fromList [ (tname x, x) | x <- xs ]
  types' <- gets (toMap . types)
  let pr' = Problem types' preds' funs' inputs'
  return pr'

infer :: (?monotone :: Type Name -> DomainSize, ?size :: Type Name -> DomainSize) =>
         Problem Formula Name -> Problem Formula Name
infer pr = rename name' res
  where (res0, uf) = runUF initial (evalStateT go s0)
        name' = name baseName res
        res = rename getRep res0
        getRep x = evalUF uf (rep x)
        s0 = S (error "infer: funs") (error "infer: preds") 1 []
        go = do
          let adapt f ty = 
                f (Type (name' (getRep (tname ty))) (error "infer: monotone") (error "infer: size") (tclass ty))
          let ?monotone = adapt ?monotone
              ?size = adapt ?size
          inferProblem pr
