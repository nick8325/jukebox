{-# LANGUAGE GADTs #-}
module Monotonox.ToFOF where

import Clausify(split, removeEquiv, run, withName)
import Name
import qualified NameMap
import Form
import Options
import qualified Data.ByteString.Char8 as BS
import Control.Monad hiding (guard)

data Scheme = Scheme {
  makeFunction :: Type -> NameM Function,
  scheme1 :: (Type -> Bool) -> (Type -> Function) -> Scheme1
  }

data Scheme1 = Scheme1 {
  forAll :: Bind Form -> Form,
  exists :: Bind Form -> Form,
  equals :: Term -> Term -> Form,
  funcAxiom :: Function -> NameM Form,
  typeAxiom :: Type -> NameM Form
  }

guard :: Scheme1 -> (Type -> Bool) -> Input Form -> Input Form
guard scheme mono (Input t k f) = Input t k (aux (pos k) f)
  where aux pos (ForAll (Bind vs f))
          | pos = forAll scheme (Bind vs (aux pos f))
          | otherwise = Not (exists scheme (Bind vs (Not (aux pos f))))
        aux pos (Exists (Bind vs f))
          | pos = exists scheme (Bind vs (aux pos f))
          | otherwise = Not (forAll scheme (Bind vs (Not (aux pos f))))
        aux pos (Literal (Pos (t :=: u)))
          | not (mono (typ t)) = equals scheme t u
        aux pos (Literal (Neg (t :=: u)))
          | not (mono (typ t)) = Not (equals scheme t u)
        aux pos l@Literal{} = l
        aux pos (Not f) = Not (aux (not pos) f)
        aux pos (And fs) = And (fmap (aux pos) fs)
        aux pos (Or fs) = Or (fmap (aux pos) fs)
        aux pos (Equiv _ _) = error "ToFOF.guard: equiv should have been eliminated (internal error)"
        aux pos (Connective _ _ _) = error "ToFOF.guard: connective should have been eliminated (internal error)"
        pos Axiom = True
        pos Conjecture = False

translate, translate1 :: Scheme -> (Type -> Bool) -> Problem Form -> Problem Form
translate1 scheme mono f = close f $ \inps -> do
  let tys = types inps
      funcs = functions inps
      -- Hardly any use adding guards if there's only one type.
      mono' | length tys == 1 = const True
            | otherwise = mono
  typeFuncs <- mapM (makeFunction scheme) tys
  let typeMap = NameMap.fromList (zipWith (:::) tys typeFuncs)
      lookupType ty =
        case NameMap.lookup (name ty) typeMap of
          Just (_ ::: f) -> f
          Nothing -> error "ToFOF.translate: type not found (internal error)"
      scheme1' = scheme1 scheme mono' lookupType
  funcAxioms <- mapM (funcAxiom scheme1') funcs
  typeAxioms <- mapM (typeAxiom scheme1') tys
  let axioms =
        map (simplify . ForAll . bind) . split . simplify . foldr (/\) true $
          funcAxioms ++ typeAxioms
  return $
    [ Input (BS.pack ("types" ++ show i)) Axiom axiom | (axiom, i) <- zip axioms [1..] ] ++
    map (guard scheme1' mono') inps

translate scheme mono f =
  let f' =
        close f $ \inps -> do
          forM inps $ \(Input tag kind f) -> do
            let prepare f = fmap (foldr (/\) true) (run (withName tag (removeEquiv (simplify f))))
            fmap (Input tag kind) $
              case kind of
                Axiom -> prepare f
                Conjecture -> fmap notInwards (prepare (nt f))
      typeI = Type nameI (Finite 0) Infinite 0
  in close (translate1 scheme mono f') (return . mapType (const typeI))

-- Typing functions.

tagsFlags :: OptionParser Bool
tagsFlags =
  bool "more-axioms"
    ["Add extra typing axioms for function arguments,",
     "when using typing tags.",
     "These are unnecessary for completeness but may help (or hinder!) the prover."]

tags :: Bool -> Scheme
tags moreAxioms = Scheme
  { makeFunction = \ty -> do
      name <- newName (BS.append (BS.pack "to_") (baseName ty))
      return (name ::: FunType [ty] ty),
    scheme1 = tags1 moreAxioms }

tags1 :: Bool -> (Type -> Bool) -> (Type -> Function) -> Scheme1
tags1 moreAxioms mono fs = Scheme1
  { forAll = ForAll,
    exists = \(Bind vs f) ->
       let bound = foldr (/\) true (map guard (NameMap.toList vs))
           guard v | mono (typ v) = true
                   | otherwise = Literal (Pos (fs (typ v) :@: [Var v] :=: Var v))
       in Exists (Bind vs (simplify bound /\ f)),
    equals =
      \t u ->
        let protect t@Var{} = fs (typ t) :@: [t]
            protect t = t
        in Literal (Pos (protect t :=: protect u)),
    funcAxiom = tagsAxiom moreAxioms mono fs,
    typeAxiom = \ty -> if moreAxioms then tagsAxiom False mono fs (fs ty) else return true }

tagsAxiom :: Bool -> (Type -> Bool) -> (Type -> Function) -> Function -> NameM Form
tagsAxiom moreAxioms mono fs f@(_ ::: FunType args res) = do
  vs <- forM args $ \ty -> do
    n <- newName "X"
    return (Var (n ::: ty))
  let t = f :@: vs
      at n f xs = take n xs ++ [f (xs !! n)] ++ drop (n+1) xs
      tag t = fs (typ t) :@: [t]
      equate (ty, t') | mono ty = true
                      | otherwise = t `eq` t'
      t `eq` u | typ t == O = Literal (Pos (Tru t)) `Equiv` Literal (Pos (Tru u))
               | otherwise = Literal (Pos (t :=: u))
      ts = (typ t, tag t):
           [ (typ (vs !! n), f :@: at n tag vs)
           | moreAxioms,
             n <- [0..length vs-1] ]
  return (foldr (/\) true (map equate ts))

-- Typing predicates.

guards :: Scheme
guards = Scheme
  { makeFunction = \ty -> do
      name <- newName (BS.append (BS.pack "is_") (baseName ty))
      return (name ::: FunType [ty] O),
    scheme1 = guards1 }

guards1 :: (Type -> Bool) -> (Type -> Function) -> Scheme1
guards1 mono ps = Scheme1
  { forAll = \(Bind vs f) ->
       let bound = foldr (/\) true (map guard (NameMap.toList vs))
           guard v | mono (typ v) = true
                   | not (naked True v f) = true
                   | otherwise = Literal (Pos (Tru (ps (typ v) :@: [Var v])))
       in ForAll (Bind vs (simplify (Not bound) \/ f)),
    exists = \(Bind vs f) ->
       let bound = foldr (/\) true (map guard (NameMap.toList vs))
           guard v | mono (typ v) = true
                   | not (naked True v f) = true
                   | otherwise = Literal (Pos (Tru (ps (typ v) :@: [Var v])))
       in Exists (Bind vs (simplify bound /\ f)),
    equals = \t u -> Literal (Pos (t :=: u)),
    funcAxiom = guardsAxiom mono ps,
    typeAxiom = guardsTypeAxiom mono ps }

naked :: Symbolic a => Bool -> Variable -> a -> Bool
naked pos v f =
  case (typeRep f, f, unpack f) of
    (FormRep, Not f, _) -> naked (not pos) v f
    (SignedRep, Pos f, _) -> naked pos v f
    (SignedRep, Neg f, _) -> naked (not pos) v f
    (AtomicRep, t :=: u, _) | pos -> t == Var v || u == Var v
    (BindRep, Bind vs f, _) -> not (NameMap.member v vs) && naked pos v f
    (_, _, Const _) -> False
    (_, _, Unary _ x) -> naked pos v x
    (_, _, Binary _ x y) -> naked pos v x || naked pos v y

guardsAxiom :: (Type -> Bool) -> (Type -> Function) -> Function -> NameM Form
guardsAxiom mono ps f@(_ ::: FunType args res)
  | mono res = return true
  | otherwise = do
    vs <- forM args $ \ty -> do
      n <- newName "X"
      return (Var (n ::: ty))
    return (Literal (Pos (Tru (ps res :@: [f :@: vs]))))

guardsTypeAxiom :: (Type -> Bool) -> (Type -> Function) -> Type -> NameM Form
guardsTypeAxiom mono ps ty
  | mono ty = return true
  | otherwise = do
    n <- newName "X"
    return (Exists (bind (Literal (Pos (Tru (ps ty :@: [Var (n ::: ty)]))))))
