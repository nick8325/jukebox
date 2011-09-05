-- Template Haskell stuff to help with the Symbolic class.

{-# LANGUAGE TemplateHaskell #-}
module UniverseTH where

import Language.Haskell.TH
import Control.Monad
import Data.List

data Constructor = C Name [TyVarBndr] Cxt Type deriving Show

constructors :: Name -> Q [Constructor]
constructors ty = do
  TyConI (DataD _ _  _ cons _) <- reify ty
  let name (NormalC x _) = x
      name (ForallC _ _ x) = name x
      norm n (ForallT tvs ctx (AppT _ ty)) = C n tvs ctx ty
      norm n (AppT _ ty) = C n [] [] ty
  forM cons $ \x -> do
    DataConI n t _ _ <- reify (name x)
    return (norm n t)

symbolicInstances :: Name -> Name -> Name -> Q [Dec]
symbolicInstances ty cls typeRep = do
  cs <- constructors ty
  forM cs $ \(C n tvs ctx ty) -> do
    let con = return (ConE n)
    decl <- [d| typeRep _ = $(con) |]
    return (InstanceD ctx (AppT (ConT cls) ty) decl)

mkUnpack :: Name -> ExpQ -> ExpQ -> ExpQ
mkUnpack ty unpack typeRep = do
  cs <- constructors ty
  let constructor (C n tvs cxt ty) = do
        e <- unpack
        return (Match (ConP n []) (NormalB e) [])
  liftM2 CaseE typeRep (mapM constructor cs)

specialiseSymbolic :: Name -> Name -> [Q Type] -> Q [Dec]
specialiseSymbolic cls f tys = aux -- `recover` error "Couldn't specialise symbolic function"
  where
    aux = do
      VarI _ ty@(ForallT _ ctx _) _ _ <- reify f
      tys' <- sequence tys
      let sym = [ v | ClassP cls' [v] <- ctx, cls == cls' ]
          instances = sequence [ [ (v, ty) | ty <- tys' ] | v <- sym ]
          subst s (ForallT tys ctx ty) =
            ForallT (tys \\ [ PlainTV v | (VarT v, _) <- s ])
                    (ctx \\ [ ClassP cls [v] | (v, _) <- s ])
                    (subst s ty)
          subst s ty@VarT{} =
            case lookup ty s of
              Nothing -> ty
              Just ty' -> ty'
          subst s (SigT ty k) = SigT (subst s ty) k
          subst s (AppT t u) = AppT (subst s t) (subst s u)
          subst s ty = ty
      return [ PragmaD (SpecialiseP f (subst inst ty) Nothing)
             | inst <- instances ]
