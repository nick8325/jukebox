-- A pretty-printer for SMTLIB.

{-# LANGUAGE CPP, OverloadedStrings #-}
module Jukebox.SMTLIB where

#include "errors.h"
import Data.Char
import Text.PrettyPrint.HughesPJ
import Jukebox.Form
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Jukebox.Name
import Jukebox.Utils
import Jukebox.TPTP.Print(prettyNames)
import Text.PrettyPrint.HughesPJClass
import Data.Maybe
import Data.Ratio
#if __GLASGOW_HASKELL__ < 710
import Control.Applicative hiding (empty)
#endif

keywords :: [String]
keywords =
    [ "ac"
    , "and"
    , "axiom"
    , "inversion"
    , "bit0"
    , "bit1"
    , "bitv"
    , "bool"
    , "check"
    , "cut"
    , "distinct"
    , "else"
    , "exists"
    , "false"
    , "forall"
    , "function"
    , "goal"
    , "if"
    , "in"
    , "include"
    , "int"
    , "let"
    , "logic"
    , "not"
    , "or"
    , "predicate"
    , "prop"
    , "real"
    , "rewriting"
    , "then"
    , "true"
    , "type"
    , "unit"
    , "void"
    , "with"
    , "assert", "check-sat"
    , "abs", "min", "max", "const"
    , "mod", "div"
    , "=", "=>", "+", "-", "*", ">", ">=", "<", "<=", "@", "!"
    , "as"
    , "declare-datatypes"
    , "declare-sort"
    , "declare-const"
    , "declare-const"
    , "declare-fun"
    , "declare-fun"
    , "define-fun"
    , "define-fun"
    , "define-fun-rec"
    , "define-fun-rec"
    , "define-funs-rec"
    , "check-sat"
    -- TIP:
    , "par"
    , "case"
    , "match"
    , "assert"
    , "assert-not"
    -- Z3:
    , "Bool", "Int", "Array", "List", "insert"
    , "isZero"
    , "map"
    , "select"
    , "subset", "union", "intersect"
    -- CVC4:
    , "concat", "member"
    ] ++ map snd renamings

renamings :: [(String, String)]
renamings =
  [("$i", "individual"),
   ("$int", "Int"),
   ("$rat", "Real"),
   ("$real", "Real"),
   ("$sum", "+"),
   ("$product", "*"),
   ("$quotient", "/"),
   ("$difference", "-"),
   ("$uminus", "-"),
   ("$is_int", "IsInt"),
   ("$to_int", "to_int"),
   ("$to_real", "to_real"),
   ("$less", "<"),
   ("$lesseq", "<="),
   ("$greater", ">"),
   ("$greatereq", ">=")]

-- Both the following functions expect prettyNames to have been used first
-- (no Unique names).
renameAvoidingKeywords :: Symbolic a => a -> NameM a
renameAvoidingKeywords x = do
  -- Allocate a new name for every reserved word
  sub <- Map.fromList <$> sequence
    [ do n <- newName ("smt_" ++ k)
         return (k, n)
    | k <- keywords ]
  return (mapName (\x -> Map.findWithDefault x (show x) sub) x)

renameTPTP :: Symbolic a => a -> a
renameTPTP = mapName f
  where
    f x = fromMaybe x (fmap name (lookup (show x) renamings))

showProblem :: Problem Form -> String
showProblem = show . pPrintProblem
    
pPrintProblem :: Problem Form -> Doc
pPrintProblem prob0 =
  vcat (pPrintDecls prob ++ map pPrintInput prob ++ [sexp ["check-sat"]])
  where
    prob = renameTPTP (prettyNames (run (prettyNames prob0) renameAvoidingKeywords))

pPrintDecls :: Problem Form -> [Doc]
pPrintDecls prob =
  map typeDecl (filter (not . builtIn) (usort (types prob))) ++
  map funcDecl (filter (not . builtIn) (usort (functions prob)))
  where
    builtIn x =
      (show (name x) /= "individual" && show (name x) `elem` map snd renamings) ||
      case name x of
        Fixed Integer{} -> True
        Fixed Rational{} -> True
        Fixed Real{} -> True
        _ -> False

    typeDecl O = empty
    typeDecl ty =
      sexp ["declare-sort", pPrintType ty, text "0"]

    funcDecl (f ::: FunType args res) =
      sexp $
        ["declare-fun", pPrint f, sexp (map pPrintType args), pPrintType res]

sexp :: [Doc] -> Doc
sexp = parens . fsep

pPrintName :: Name -> Doc
pPrintName (Fixed (Integer n)) = pPrint n
pPrintName (Fixed (Rational n)) =
  sexp ["/", pPrint (numerator n), pPrint (denominator n)]
pPrintName (Fixed (Real n)) =
  sexp ["/", pPrint (numerator n), pPrint (denominator n)]
pPrintName x = text . escape . show $ x
  where
    escape xs
      | all isOk xs = xs
      | otherwise = "|" ++ concatMap escapeSym xs ++ "|"

    isOk c
      | isAlphaNum c = True
      | c `elem` ("~!@$%^&*_-+=<>.?/" :: String) = True
      | otherwise = False

    escapeSym '|' = "\\|"
    escapeSym '\\' = "\\\\"
    escapeSym c = [c]

pPrintType :: Type -> Doc
pPrintType O = "Bool"
pPrintType ty = pPrintName (name ty)

pPrintInput :: Input Form -> Doc
pPrintInput Input{kind = Axiom _, what = form} =
  sexp ["assert", pPrintForm form]
pPrintInput Input{kind = Conjecture, what = form} =
  sexp ["assert", sexp ["not", pPrintForm form]]
pPrintInput Input{kind = Question, what = form} =
  sexp ["assert", sexp ["not", pPrintForm form]]

pPrintForm :: Form -> Doc
pPrintForm (Literal (Pos l)) = pPrintAtomic l
pPrintForm (Literal (Neg l)) = sexp ["not", pPrintAtomic l]
pPrintForm (Not f) = sexp ["not", pPrintForm f]
pPrintForm (And ts) = sexp ("and":map pPrintForm ts)
pPrintForm (Or ts) = sexp ("or":map pPrintForm ts)
pPrintForm (Equiv t u) = sexp ["=", pPrintForm t, pPrintForm u]
pPrintForm (Connective Implies t u) = sexp ["=>", pPrintForm t, pPrintForm u]
pPrintForm (Connective Follows t u) = sexp ["=>", pPrintForm u, pPrintForm t]
pPrintForm (Connective Xor t u) = sexp ["xor", pPrintForm t, pPrintForm u]
pPrintForm (Connective Nor t u) = sexp ["not", sexp ["or", pPrintForm t, pPrintForm u]]
pPrintForm (Connective Nand t u) = sexp ["not", sexp ["and", pPrintForm t, pPrintForm u]]
pPrintForm (ForAll (Bind vs f)) = pPrintQuant "forall" vs f
pPrintForm (Exists (Bind vs f)) = pPrintQuant "exists" vs f

pPrintQuant :: Doc -> Set.Set Variable -> Form -> Doc
pPrintQuant q vs f
  | Set.null vs = pPrintForm f
  | otherwise =
    sexp [q,
          sexp [sexp [pPrintName x, pPrintType ty] | x ::: ty <- Set.toList vs],
          pPrintForm f]

pPrintAtomic :: Atomic -> Doc
pPrintAtomic (t :=: u) = sexp ["=", pPrintTerm t, pPrintTerm u]
pPrintAtomic (Tru t) = pPrintTerm t

pPrintTerm :: Term -> Doc
pPrintTerm (Var (x ::: _)) = pPrintName x
pPrintTerm ((f ::: _) :@: []) = pPrintName f
pPrintTerm ((f ::: _) :@: ts) = sexp (pPrintName f:map pPrintTerm ts)
