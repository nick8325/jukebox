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
    allowNonUnitConjectures :: Bool }
  deriving Show

hornFlags :: OptionParser HornFlags
hornFlags =
  inGroup "Horn clause encoding options" $
  HornFlags <$>
    bool "non-unit-conjectures"
      ["Allow conjectures to be non-unit clauses (on by default)."]
      True

hornToUnit :: HornFlags -> Problem Clause -> Either (Input Clause) (Problem Clause)
hornToUnit flags prob =
  eliminateHornClauses $
  eliminateNonUnitConjectures flags $
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

eliminateNonUnitConjectures :: HornFlags -> Problem Clause -> Problem Clause
eliminateNonUnitConjectures flags prob
  | allowNonUnitConjectures flags = prob
  | null nucs = prob
  | otherwise =
    normals ++ map (fmap addConjecture) nucs ++
    [Input { tag = "goal", kind = Ax NegatedConjecture, source = Unknown,
             what = clause [Neg (a :=: b)] }]
  where
    (nucs, normals) = partition nonUnitConjecture prob

    nonUnitConjecture c =
      all (not . pos) ls && length ls /= 1
      where
        ls = toLiterals (what c)

    addConjecture c = clause (Pos (a :=: b):toLiterals c)

    (a, b) = run prob $ \_ -> do
      token <- newType "token"
      a <- newFunction "a" [] token
      b <- newFunction "b" [] token
      return (a :@: [], b :@: [])

eliminateHornClauses :: Problem Clause -> Either (Input Clause) (Problem Clause)
eliminateHornClauses prob = do
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
      ifeq ty1 ty2 :@: [t, u, v] :=:
      ifeq ty1 ty2 :@: [t, u, w]
      where
        v :=: w = encode ls l
        ty1 = typ t
        ty2 = typ v
    
    axiom (ifeq@(_ ::: FunType [ty1, _, ty2] _)) =
      Input {
        tag = "ifeq_axiom",
        kind = Ax Axiom,
        source = Unknown,
        what = clause [Pos (ifeq :@: [x, x, y] :=: y)] }
      where
        x = Var (xvar ::: ty1)
        y = Var (yvar ::: ty2)
    
    ifeq ty1 ty2 =
      variant ifeqName [name ty1, name ty2] :::
        FunType [ty1, ty1, ty2] ty2

    isIfeq f =
      isJust $ do
        (x, _) <- unvariant (name f)
        guard (x == ifeqName)

    (ifeqName, xvar, yvar) = run prob $ \_ -> do
      ifeqName <- newName "$ifeq"
      xvar <- newName "X"
      yvar <- newName "Y"
      return (ifeqName, xvar, yvar)
