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
import Control.Monad
import qualified Data.Set as Set
import Control.Monad.Trans.RWS
import Control.Monad.Trans.List
import Control.Monad.Trans.Class

data HornFlags =
  HornFlags {
    allowNonUnitConjectures :: Bool,
    allowNonGroundConjectures :: Bool,
    allowCompoundConjectures :: Bool,
    encoding :: Encoding }
  deriving Show

data Encoding = Symmetric | Asymmetric1 | Asymmetric2
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
    bool "compound-conjectures"
      ["Allow conjectures to be compound terms (on by default)."]
      True <*>
    encoding
  where
    encoding =
      flag "conditional-encoding"
        ["Which method to use to encode conditionals (asymmetric2 by default)."]
        Asymmetric2
        (argOption
          [("symmetric", Symmetric),
           ("asymmetric1", Asymmetric1),
           ("asymmetric2", Asymmetric2)])

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
      ((not (allowCompoundConjectures flags) && or [size t > 1 | t <- terms ls]) ||
       (not (allowNonUnitConjectures flags) && length ls /= 1) ||
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
  (prob, funs) <- evalRWST (mapM elim1 prob) () 0
  return (map toInput (usort funs) ++ concat prob)
  where
    fresh base = lift $ do
      n <- get
      put $! n+1
      return (variant base [name (show n)])

    elim1 :: Input Clause -> RWST () [Atomic] Int (Either (Input Clause)) [Input Clause]
    elim1 c =
      case partition pos (toLiterals (what c)) of
        ([], _) -> return [c]
        ([Pos l], ls) -> runListT $ do
          l <- foldM encode l ls
          return c { what = clause [Pos l] }
        _ -> lift $ Left c

    encode :: Atomic -> Literal -> ListT (RWST () [Atomic] Int (Either (Input Clause))) Atomic
    encode (c :=: d) (Neg (a :=: b)) =
      let
        ty1 = typ a
        ty2 = typ c
        x = Var (xvar ::: ty1)
        y = Var (yvar ::: ty2)
        z = Var (zvar ::: ty2)
      in case encoding flags of
        Symmetric -> do
          let ifeq = variant ifeqName [name ty1, name ty2] ::: FunType [ty1, ty1, ty2] ty2
          axiom (ifeq :@: [x, x, y] :=: y)
          return (ifeq :@: [a, b, c] :=: ifeq :@: [a, b, d])
        Asymmetric1 -> do
          let
            ifeq = variant ifeqName [name ty1, name ty2] ::: FunType [ty1, ty1, ty2, ty2] ty2
          (c :=: d) <- return (swap size (c :=: d))
          axiom (ifeq :@: [x, x, y, z] :=: y)
          return (ifeq :@: [a, b, c, d] :=: d)
        Asymmetric2 -> do
          ifeqName <- fresh ifeqName
          let
            vs = Set.toList (Set.unions (map free [a, b, c, d]))
            ifeq = ifeqName ::: FunType (ty1:map typ vs) ty2
            app t = ifeq :@: (t:map Var vs)
          msum $ map return [app a :=: c, app b :=: d]

    swap f (t :=: u) =
      if f t >= f u then (t :=: u) else (u :=: t)

    axiom l = lift $ tell [l]

    toInput l =
      Input {
        tag = "ifeq_axiom",
        kind = Ax Axiom,
        source = Unknown,
        what = clause [Pos l] }

    (ifeqName, xvar, yvar, zvar) = run prob $ \_ -> do
      ifeqName <- newName "$ifeq"
      xvar <- newName "A"
      yvar <- newName "B"
      zvar <- newName "C"
      return (ifeqName, xvar, yvar, zvar)