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
import Data.List
import Data.Maybe
import Control.Monad

data HornFlags =
  HornFlags {
    allowNonUnitConjectures :: Bool,
    allowNonGroundConjectures :: Bool,
    asymmetricEncoding :: Bool }
  deriving Show

hornFlags :: OptionParser HornFlags
hornFlags =
  inGroup "Horn clause encoding options" $
  HornFlags <$>
    bool "non-unit-conjectures"
      ["Allow conjectures to be non-unit clauses (off by default)."]
      False <*>
    bool "non-ground-conjectures"
      ["Allow conjectures to be non-ground clauses (off by default)."]
      False <*>
    bool "asymmetric-encoding"
      ["Use an alternative, asymmetric encoding (off by default)."]
      False

hornToUnit :: HornFlags -> Problem Clause -> Either (Input Clause) (Problem Clause)
hornToUnit flags prob =
  eliminateHornClauses flags $
  eliminateUnsuitableConjectures flags $
  eliminatePredicates prob

eliminatePredicates :: Problem Clause -> Problem Clause
eliminatePredicates prob =
  map (fmap elim) prob
  where
    elim = clause . map (fmap elim1) . toLiterals
    elim1 (t :=: u) = t :=: u
    elim1 (Tru ((p ::: FunType tys _) :@: ts)) =
      ((p ::: FunType tys bool) :@: ts) :=: true

    (bool, true) = run prob $ \_ -> do
      bool <- newType "bool"
      true <- newFunction "true" [] bool
      return (bool, true :@: [])

eliminateUnsuitableConjectures :: HornFlags -> Problem Clause -> Problem Clause
eliminateUnsuitableConjectures flags prob
  | null bad = prob
  | otherwise =
    good ++ map (fmap addConjecture) bad ++
    [Input { tag = "goal", kind = Ax NegatedConjecture, source = Unknown,
             what = clause [Neg (a :=: b)] }]
  where
    (bad, good) = partition unsuitable prob

    unsuitable c =
      all (not . pos) ls &&
      ((not (allowNonUnitConjectures flags) && length ls /= 1) ||
       (not (allowNonGroundConjectures flags) && not (ground ls)))
      where
        ls = toLiterals (what c)

    addConjecture c = clause (Pos (a :=: b):toLiterals c)

    (a, b) = run prob $ \_ -> do
      token <- newType "token"
      a <- newFunction "a" [] token
      b <- newFunction "b" [] token
      return (a :@: [], b :@: [])

eliminateHornClauses :: HornFlags -> Problem Clause -> Either (Input Clause) (Problem Clause)
eliminateHornClauses flags prob = do
  prob <- mapM elim1 prob
  return (prob ++ map axiom (usort (filter isIfeq (functions prob))))
  where
    elim1 c =
      case partition pos (toLiterals (what c)) of
        ([], _) -> Right c
        ([l], ls) ->
          Right c { what = clause [Pos (encode ls l)] }
        _ -> Left c

    encode [] (Pos l) = l
    encode (Neg (t :=: u):ls) l =
      if not (asymmetricEncoding flags) then
        ifeq ty1 ty2 :@: [t, u, v] :=: ifeq ty1 ty2 :@: [t, u, w]
      else if size v < size w then
        ifeq ty1 ty2 :@: [t, u, w, v] :=: v
      else
        ifeq ty1 ty2 :@: [t, u, v, w] :=: w
      where
        v :=: w = encode ls l
        ty1 = typ t
        ty2 = typ v
    
    axiom (ifeq@(_ ::: FunType (ty1:_:ty2:_) _)) =
      Input {
        tag = "ifeq_axiom",
        kind = Ax Axiom,
        source = Unknown,
        what =
          if asymmetricEncoding flags then
            clause [Pos (ifeq :@: [x, x, y, z] :=: y)]
          else
            clause [Pos (ifeq :@: [x, x, y] :=: y)]}
      where
        x = Var (xvar ::: ty1)
        y = Var (yvar ::: ty2)
        z = Var (zvar ::: ty2)
    
    ifeq ty1 ty2 =
      variant ifeqName [name ty1, name ty2] :::
        if asymmetricEncoding flags then
          FunType [ty1, ty1, ty2, ty2] ty2
        else
          FunType [ty1, ty1, ty2] ty2

    isIfeq f =
      isJust $ do
        (x, _) <- unvariant (name f)
        guard (x == ifeqName)

    (ifeqName, xvar, yvar, zvar) = run prob $ \_ -> do
      ifeqName <- newName "$ifeq"
      xvar <- newName "X"
      yvar <- newName "Y"
      zvar <- newName "Z"
      return (ifeqName, xvar, yvar, zvar)
