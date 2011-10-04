{-# LANGUAGE GADTs #-}
module Monotonox.ToFOF where

import Clausify(split, removeEquivAndMiniscope, run)
import Name
import qualified NameMap
import Form
import Options
import qualified Data.ByteString.Char8 as BS
import Control.Monad hiding (guard)

data Scheme = Scheme {
  makeFunction :: Type -> NameM Function,
  selfAxioms :: Bool,
  scheme1 :: (Type -> Function) -> Scheme1
  }

data Scheme1 = Scheme1 {
  forAll :: Bind Form -> Form,
  equals :: Term -> Term -> Form,
  axiom :: (Type -> Bool) -> Function -> NameM Form
  }

guard :: Scheme1 -> (Type -> Bool) -> Input Form -> Input Form
guard scheme mono (Input t k f) = Input t k (aux (pos k) f)
  where aux pos (ForAll (Bind vs f))
          | pos = forAll scheme (Bind vs (aux pos f))
        aux pos (Exists (Bind vs f))
          | not pos = Not (forAll scheme (Bind vs (Not (aux pos f))))
        aux pos (Literal (Pos (t :=: u)))
          | pos && not (mono (typ t)) = equals scheme t u
        aux pos (Literal (Neg (t :=: u)))
          | not pos && not (mono (typ t)) = Not (equals scheme t u)
        aux pos l@Literal{} = l
        aux pos (Not f) = Not (aux (not pos) f)
        aux pos (And fs) = And (fmap (aux pos) fs)
        aux pos (Or fs) = Or (fmap (aux pos) fs)
        aux pos (Equiv _ _) = error "ToFOF.guard: equiv should have been eliminated (internal error)"
        aux pos (ForAll (Bind vs f)) = ForAll (Bind vs (aux pos f))
        aux pos (Exists (Bind vs f)) = Exists (Bind vs (aux pos f))
        aux pos (Connective _ _ _) = error "ToFOF.guard: connective should have been eliminated (internal error)"
        pos Axiom = True
        pos Conjecture = False

translate, translate1 :: Scheme -> (Type -> Bool) -> Problem Form -> Problem Form
translate1 scheme mono f = close f $ \inps -> do
  let tys = types inps
      funcs = functions inps
  typeFuncs <- mapM (makeFunction scheme) tys
  let typeMap = NameMap.fromList (zipWith (:::) tys typeFuncs)
      lookupType ty =
        case NameMap.lookup (name ty) typeMap of
          Just (_ ::: f) -> f
          Nothing -> error "ToFOF.translate: type not found (internal error)"
      scheme1' = scheme1 scheme lookupType
  axioms <-
    fmap (split . simplify . ForAll . bind . foldr (/\) true)
      (mapM (axiom scheme1' mono) (funcs ++ concat [ typeFuncs | selfAxioms scheme ]))
  return $
    [ Input (BS.pack ("types" ++ show i)) Axiom axiom | (axiom, i) <- zip axioms [1..] ] ++
    map (guard scheme1' mono) inps

translate scheme mono f =
  let f' =
        close f $ \inps -> do
          forM inps $ \(Input tag kind f) -> do
            let prepare f = fmap (foldr (/\) true) (run (removeEquivAndMiniscope tag f))
            fmap (Input tag kind) $
              case kind of
                Axiom -> prepare f
                Conjecture -> fmap nt (prepare (nt f))
  in translate1 scheme mono f'

-- Typing functions.

tagsFlags :: OptionParser Bool
tagsFlags =
  bool "more-axioms"
    ["Add extra typing axioms for function arguments.",
     "These are unnecessary for completeness but may help (or hinder!) the prover."]

tags :: Bool -> Scheme
tags moreAxioms = Scheme
  { makeFunction = \ty -> do
      name <- newName (BS.append (BS.pack "tag_") (baseName ty))
      return (name ::: FunType [ty] ty),
    selfAxioms = moreAxioms,
    scheme1 = tags1 moreAxioms }

tags1 :: Bool -> (Type -> Function) -> Scheme1
tags1 moreAxioms fs = Scheme1
  { forAll = ForAll,
    equals =
      \t u ->
        let protect t@Var{} = fs (typ t) :@: [t]
            protect t = t
        in Literal (Pos (protect t :=: protect u)),
    axiom = tagsAxiom moreAxioms fs }

tagsAxiom :: Bool -> (Type -> Function) -> (Type -> Bool) -> Function -> NameM Form
tagsAxiom moreAxioms fs mono f@(_ ::: FunType args res) = do
  vs <- forM args $ \ty -> do
    n <- newName "X"
    return (Var (n ::: ty))
  let t = f :@: vs
      at n f xs = take n xs ++ [f (xs !! n)] ++ drop (n+1) xs
      tag t = fs (typ t) :@: [t]
      equate t' | mono (typ t) = true
                | otherwise = Literal (Pos (t :=: t'))
      ts = tag t:[ f :@: at n tag vs
                 | moreAxioms,
                   n <- [0..length vs-1] ]
  return (foldr (/\) true (map equate ts))
