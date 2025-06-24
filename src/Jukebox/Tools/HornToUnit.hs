-- | Encodes Horn problems as unit equalities.
module Jukebox.Tools.HornToUnit where

-- To translate Horn problems where the only predicate is equality, we use the
-- following translation.
--
-- We introduce a predicate $ifeq : A * A * B > B at (conceptually) each pair
-- of types A and B, together with the axiom
--   $ifeq(X, X, Y) = Y.
--
-- A conditional equation a = b => c = d is encoded as
--   $ifeq(a, b, c) = $ifeq(a, b, d)
--
-- When encoding equations with multiple conditions we proceed from the inside
-- out so that, for example
--   a = b & c = d => e = f
-- would become
--   a = b => $ifeq(c, d, e) = $ifeq(c, d, f)
-- which in turn becomes
--   $ifeq(a, b, $ifeq(c, d, e)) = $ifeq(a, b, $ifeq(c, d, f))
--
-- We encode predicates p(X) as equations p(X)=true, i.e., we introduce a new
-- type bool and term true : bool, and transform predicates into functions
-- to bool.

import Jukebox.Form
import Jukebox.Name
import Jukebox.Options
import Jukebox.Utils
import qualified Jukebox.Sat as Sat
import Data.List
import Control.Monad
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Control.Monad.Trans.RWS
import Control.Monad.Trans.Class

data HornFlags =
  HornFlags {
    allowConjunctiveConjectures :: Bool,
    allowDisjunctiveConjectures :: Bool,
    allowNonGroundConjectures :: Bool,
    allowCompoundConjectures :: Bool,
    dropNonHorn :: Bool,
    passivise :: Bool,
    multi :: Bool,
    smaller :: Bool,
    encoding :: Encoding }
  deriving Show

data Encoding = Symmetric | Asymmetric1 | Asymmetric2 | Asymmetric3
  deriving (Eq, Show)

hornFlags :: OptionParser HornFlags
hornFlags =
  inGroup "Horn clause encoding options" $
  HornFlags <$>
    bool "conjunctive-conjectures"
      ["Allow conjectures to be conjunctions of equations (on by default)."]
      True <*>
    bool "disjunctive-conjectures"
      ["Allow conjectures to be disjunctions of equations (on by default)."]
      True <*>
    bool "non-ground-conjectures"
      ["Allow conjectures to be non-ground clauses (on by default)."]
      True <*>
    bool "compound-conjectures"
      ["Allow conjectures to be compound terms (on by default)."]
      True <*>
    bool "drop-non-horn"
      ["Silently drop non-Horn clauses from input problem (off by default)."]
      False <*>
    bool "passivise"
      ["Encode problem so as to get fewer critical pairs (off by default)."]
      False <*>
    bool "multi"
      ["Encode multiple left-hand sides at once (off by default)."]
      False <*>
    bool "smaller"
      ["Swap ordering of certain equations (off by default)"]
      False <*>
    encoding
  where
    encoding =
      flag "conditional-encoding"
        ["Which method to use to encode conditionals (if-then-else by default)."]
        Asymmetric1
        (argOption
          [("if-then", Symmetric),
           ("if-then-else", Asymmetric1),
           ("fresh", Asymmetric2),
           ("if", Asymmetric3)])

hornToUnit :: HornFlags -> Problem Clause -> IO (Either (Input Clause) (Either Answer (Problem Clause)))
hornToUnit flags prob = do
  res <- encodeTypesSmartly prob
  return $
    case res of
      Left ans ->
        Right (Left ans)
      Right enc ->
        fmap (Right . enc) $
        eliminateHornClauses flags $
        eliminateUnsuitableConjectures flags $
        eliminateMultiplePreconditions flags $
        eliminatePredicates prob

eliminatePredicates :: Problem Clause -> Problem Clause
eliminatePredicates prob =
  map (fmap elim) prob
  where
    elim = clause . map (fmap elim1) . toLiterals
    elim1 (t :=: u) = t :=: u
    elim1 (Tru ((p ::: FunType tys _) :@: ts)) =
      ((p ::: FunType tys bool) :@: ts) :=: true

    (bool, true) = run_ prob $ do
      bool <- newType (withLabel "bool" (name "bool"))
      true <- newFunction (withLabel "true" (name "true")) [] bool
      return (bool, true :@: [])

eliminateMultiplePreconditions :: HornFlags -> Problem Clause -> Problem Clause
eliminateMultiplePreconditions flags prob
  | otherwise =
    map elim prob
    where
      elim inp
        | (null poss && length negs /= 1 && not (allowConjunctiveConjectures flags)) ||
          (not (null poss) && length negs > 1 && multi flags) =
          inp{what = clause (Neg ((tuple tys :@: ts) :=: (tuple tys :@: us)):poss)}
        where
          (poss, negs) = partition pos (toLiterals (what inp))
          ts = [t | l <- negs, let Neg (t :=: _) = l]
          us = [u | l <- negs, let Neg (_ :=: u) = l]
          tys = map typ ts
      elim inp = inp

      tuple = run_ prob $ do
        tupleType <- newName (withLabel "tuple" (name "tuple"))
        tuple <- newName (withLabel "tuple" (name "tuple"))
        return $ \args ->
          variant tuple args :::
          FunType args (Type (variant tupleType args))

eliminateUnsuitableConjectures :: HornFlags -> Problem Clause -> Problem Clause
eliminateUnsuitableConjectures flags prob
  | null bad = prob
  | otherwise =
    good ++ map (fmap addConjecture) bad ++
    [Input { ident = Nothing, tag = "goal", kind = Ax NegatedConjecture, source = Unknown,
             what = clause [Neg (a :=: b)] }]
  where
    (bad, good) = partition unsuitable prob

    ngoals = length $ filter (all (not . pos) . toLiterals . what) prob

    unsuitable c =
      all (not . pos) ls &&
      ((not (allowCompoundConjectures flags) && or [size t > 1 | t <- terms ls]) ||
       (not (allowDisjunctiveConjectures flags) && ngoals > 1) ||
       (not (allowNonGroundConjectures flags) && not (ground ls)))
      where
        ls = toLiterals (what c)

    addConjecture c = clause (Pos (a :=: b):toLiterals c)

    (a, b) = run_ prob $ do
      token <- newType (withLabel "token" (name "token"))
      a <- newFunction (withLabel "token_a" (name "a")) [] token
      b <- newFunction (withLabel "token_b" (name "b")) [] token
      return (a :@: [], b :@: [])

eliminateHornClauses :: HornFlags -> Problem Clause -> Either (Input Clause) (Problem Clause)
eliminateHornClauses flags prob = do
  (prob, funs) <- evalRWST (mapM elim1 prob) () 0
  return (map toInput (usort funs) ++ concat prob)
  where
    fresh base = do
      n <- get
      put $! n+1
      return (variant base [name (show n)])

    passiveFresh (x ::: ty)
      | passivise flags = fmap (::: ty) (fresh x)
      | otherwise = return (x ::: ty)

    passive (Var x) = Var x
    passive ((f ::: ty) :@: ts) =
      (variant f [passiveName] ::: ty) :@: map passive ts

    elim1 :: Input Clause -> RWST () [(String, Atomic)] Int (Either (Input Clause)) [Input Clause]
    elim1 c =
      case partition pos (toLiterals (what c)) of
        ([], _) -> return [c]
        ([Pos l], ls) -> do
          l <- foldM (encode (tag c)) l ls
          return [c { what = clause [Pos l] }]
        _ ->
          if dropNonHorn flags then
            return []
          else
            lift $ Left c

    encode :: String -> Atomic -> Literal -> RWST () [(String, Atomic)] Int (Either (Input Clause)) Atomic
    encode tag (c :=: d) (Neg (a :=: b)) =
      let
        ty1 = typ a
        ty2 = typ c
        x = Var (xvar ::: ty1)
        y = Var (yvar ::: ty2)
        z = Var (zvar ::: ty2)
      in case encoding flags of
        -- ifeq(x, x, y) = y
        -- ifeq(a, b, c) = ifeq(a, b, d)
        Symmetric -> do
          ifeq <- passiveFresh (variant ifeqName [name ty1, name ty2] ::: FunType [ty1, ty1, ty2] ty2)
          if passivise flags then do
            axiom (tag, ifeq :@: [x, x, passive c] :=: c)
            axiom (tag, ifeq :@: [x, x, passive d] :=: d)
            return (ifeq :@: [a, b, passive c] :=: ifeq :@: [a, b, passive d])
           else do
            axiom ("ifeq_axiom", ifeq :@: [x, x, y] :=: y)
            return (ifeq :@: [a, b, c] :=: ifeq :@: [a, b, d])
        -- ifeq(x, x, y, z) = y
        -- ifeq(a, b, c, d) = d
        Asymmetric1 -> do
          ifeq <- passiveFresh (variant ifeqName [name ty1, name ty2] ::: FunType [ty1, ty1, ty2, ty2] ty2)
          ~(c :=: d) <- return (swap size (c :=: d))
          if passivise flags then do
            axiom ("ifeq_axiom", ifeq :@: [x, x, passive c, y] :=: c)
            return (ifeq :@: [a, b, passive c, passive d] :=: d)
           else do
            axiom ("ifeq_axiom", ifeq :@: [x, x, y, z] :=: y)
            return (ifeq :@: [a, b, c, d] :=: d)
        -- f(a, sigma) = c
        -- f(b, sigma) = d
        -- where sigma = FV(a, b, c, d)
        Asymmetric2 -> do
          ifeqName <- fresh freshName
          ~(a :=: b) <- return (swap size (a :=: b))
          ~(c :=: d) <- return (swap size (c :=: d))
          let
            vs =
              if passivise flags then
                map passive [a, b, c, d]
              else
                map Var (Set.toList (Set.unions (map free [a, b, c, d])))
            ifeq = ifeqName ::: FunType (ty1:map typ vs) ty2
            app t = ifeq :@: (t:vs)
          if smaller flags then do
            axiom (tag, app b :=: d)
            return (app a :=: c)
           else do
            axiom (tag, app a :=: c)
            return (app b :=: d)
        -- f(a, b, sigma) = c
        -- f(x, x, sigma) = d
        -- where sigma = FV(c, d)
        Asymmetric3 -> do
          ifeqName <- fresh freshName
          ~(c :=: d) <- return (swap size (c :=: d))
          let
            vs =
              if passivise flags then
                map passive [c, d]
              else
                map Var (Set.toList (Set.unions (map free [c, d])))
            ifeq = ifeqName ::: FunType (ty1:ty1:map typ vs) ty2
            app t u = ifeq :@: (t:u:vs)
            x = Var (xvar ::: ty1)
          axiom (tag, app x x :=: c)
          return (app a b :=: d)

    swap f (t :=: u) =
      (\(t :=: u) -> if smaller flags then u :=: t else t :=: u) $
      if f t >= f u then (t :=: u) else (u :=: t)

    axiom l = tell [l]

    toInput (tag, l) =
      Input {
        ident = Nothing,
        tag = tag,
        kind = Ax Axiom,
        source = Unknown,
        what = clause [Pos l] }

    (ifeqName, freshName, passiveName, xvar, yvar, zvar) = run_ prob $ do
      ifeqName <- newName (withLabel "ifeq" (name "ifeq"))
      freshName <- newName (withLabel "fresh" (name "fresh"))
      passiveName <- newName (withLabel "passive" (name "passive"))
      xvar <- newName "A"
      yvar <- newName "B"
      zvar <- newName "C"
      return (ifeqName, freshName, passiveName, xvar, yvar, zvar)

-- Soundly encode types, but try to erase them if possible.
-- Based on the observation that if the input problem is untyped,
-- erasure is sound unless:
--   * the problem is satisfiable
--   * but the only model is of size 1.
-- We therefore check if there is a model of size 1. This is easy
-- (the term structure collapses), and if so, we return the SZS
-- status directly instead.
encodeTypesSmartly :: Problem Clause -> IO (Either Answer (Problem Clause -> Problem Clause))
encodeTypesSmartly prob
  | isFof prob = do
    sat <- hasSizeOneModel prob
    if sat then
      return $ Left $
        Sat Satisfiable $ Just
         ["There is a model where all terms are equal, ![X,Y]:X=Y."]
      else return (Right eraseTypes)
  | otherwise =
    return (Right id)

-- Check if a problem has a model of size 1.
-- Done by erasing all terms from the problem.
hasSizeOneModel :: Problem Clause -> IO Bool
hasSizeOneModel p = do
  s <- Sat.newSolver
  let funs = functions p
  lits <- replicateM (length funs) (Sat.newLit s)
  let
    funMap = Map.fromList (zip funs lits)
    transClause (Clause (Bind _ ls)) =
      map transLit ls
    transLit (Pos a) = transAtom a
    transLit (Neg a) = Sat.neg (transAtom a)
    transAtom (Tru (p :@: _)) =
      Map.findWithDefault undefined p funMap
    transAtom (_ :=: _) = Sat.true
  mapM_ (Sat.addClause s . transClause) (map what p)
  Sat.solve s [] <* Sat.deleteSolver s
