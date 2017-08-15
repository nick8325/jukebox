-- Pretty-printing of formulae. WARNING: icky code inside!
{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, TypeOperators, FlexibleInstances, CPP, GADTs, PatternGuards #-}
module Jukebox.TPTP.Print(prettyShow, prettyNames, showClauses, pPrintClauses, showProblem, pPrintProblem, pPrintProof)
       where

#include "errors.h"
import Data.Char
import Data.Maybe
import Text.PrettyPrint.HughesPJ
import qualified Jukebox.TPTP.Lexer as L
import Jukebox.Form
import qualified Data.Map.Strict as Map
import Data.Map(Map)
import qualified Data.Set as Set
import Data.Set(Set)
import Jukebox.Name
import Jukebox.Utils
import Text.PrettyPrint.HughesPJClass
import Control.Monad.Trans.State.Strict

pPrintClauses :: Problem Clause -> Doc
pPrintClauses prob0
  | isReallyFof prob = vcat (map (pPrintInput "cnf" pPrint) prob)
  | otherwise = pPrintProblem "tcf" (map (fmap toForm) prob)
  where
    prob = prettyNames prob0

showClauses :: Problem Clause -> String
showClauses = show . pPrintClauses

pPrintProblem :: String -> Problem Form -> Doc
-- "kind" is only used if the problem is typed
pPrintProblem kind prob0
  | isReallyFof prob = vcat (map (pPrintInput "fof" (pPrintFof 0)) prob)
  | otherwise = vcat (pPrintDecls kind prob ++ map (pPrintInput kind (pPrintTff 0)) prob)
  where
    prob = prettyNames prob0

-- Print a problem together with all source/derivation information.
pPrintProof :: Problem Form -> Doc
pPrintProof prob =
  pPrintAnnotProof (evalState (concat <$> mapM annot prob) (1, Map.empty))
  where
    fun f [] = text f
    fun f xs = text f <> parens (fsep (punctuate comma xs))
    list = brackets . fsep . punctuate comma

    clause n = "c" ++ show n

    info inp = (kind inp, what inp)

    -- We maintain: the set of formulas printed so far,
    -- and the highest number given so far.
    findNumber :: Input Form -> State (Int, Map (Kind, Form) Int) (Maybe Int)
    findNumber inp =
      gets (Map.lookup (info inp) . snd)

    newNumber :: Input Form -> State (Int, Map (Kind, Form) Int) (Maybe Int)
    newNumber inp = do
      (n, map) <- get
      case Map.lookup (info inp) map of
        Nothing -> do
          put (n+1, Map.insert (info inp) n map)
          return (Just n)
        Just _ -> return Nothing

    annot :: Input Form -> State (Int, Map (Kind, Form) Int) [(Input Form, (String, [Doc]))]
    annot inp
      -- Formula is identical to its parent
      | Inference _ _ [inp'] <- source inp,
          let [p, q] = prettyNames [what inp, what inp'] in
          kind inp == kind inp' &&
          -- I have NO idea why this doesn't work without show here :(
          show p == show q =
            annot inp { source = source inp' }
      | otherwise = do
          mn <- findNumber inp
          case mn of
            Just _ ->
              -- Already processed this formula
              return []
            Nothing -> do
              let
                ret k stuff = do
                  res <- newNumber inp
                  case res of
                    Just n ->
                      return [(inp { tag = clause n }, (k, stuff))]
                    Nothing ->
                      return []

              case source inp of
                Unknown -> ret "plain" []
                FromFile file _ ->
                  ret (show (kind inp))
                    [fun "file" [text (escapeAtom file), text (escapeAtom (tag inp))]]
                Inference name status parents -> do
                  -- Process all parents first
                  rest <- mapM annot parents
                  nums <- map fromJust <$> mapM findNumber parents

                  fmap (concat rest ++) $
                    ret "plain"
                      [fun "inference" [
                        text name, list [fun "status" [text status]],
                        list [text (clause n) | n <- nums]]]

pPrintAnnotProof :: [(Input Form, (String, [Doc]))] -> Doc
pPrintAnnotProof annots0 =
  vcat $
    [ vcat (pPrintDecls "tff" inps) | not (isReallyFof inps) ] ++
    [ pPrintClause (family x) (tag inp) k (pp x:rest)
    | (inp, (k, rest)) <- annots,
      let x = what inp ]
  where
    inps0 = map fst annots0
    inps = prettyNames inps0
    annots = zip inps (map snd annots0)

    family x
      | isReallyFof x && isJust (toClause x) = "cnf"
      | isReallyFof x = "fof"
      | otherwise = "tff"

    pp x
      | isReallyFof x =
        case toClause x of
          Nothing -> pPrintFof 0 x
          Just cl -> pPrint cl
      | otherwise =
        pPrintTff 0 x

showProblem :: Problem Form -> String
showProblem = show . pPrintProblem "tff"

isReallyFof :: Symbolic a => a -> Bool
isReallyFof = all p . types
  where
    p O = True
    p (Type ty _ _) | ty == i = True
    p _ = False
    i = name "$i"

pPrintDecls :: String -> Problem Form -> [Doc]
pPrintDecls kind prob =
  map typeDecl (usort (types prob)) ++
  map funcDecl (usort (functions prob))
  where
    typeDecl O = empty
    typeDecl (Type ty _ _) | ty == i = empty
    typeDecl ty = typeClause ty (text "$tType")
    i = name "$i"

    funcDecl (f ::: ty) = typeClause f (pPrint ty)

    typeClause :: Show a => a -> Doc -> Doc
    typeClause name ty =
      pPrintClause kind "type" "type"
        [text (escapeAtom (show name)) <> colon <+> ty]

instance Pretty a => Pretty (Input a) where
  pPrint = pPrintInput "tff" pPrint
instance Pretty a => Show (Input a) where
  show = prettyShow

pPrintInput :: String -> (a -> Doc) -> Input a -> Doc
pPrintInput family pp i =
  pPrintClause family (tag i) (show (kind i)) [pp (what i)]

pPrintClause :: String -> String -> String -> [Doc] -> Doc
pPrintClause family name kind rest =
  text family <> parens (sep (punctuate comma ([text (escapeAtom name), text kind] ++ rest))) <> text "."

instance Pretty Clause where
  pPrint (Clause (Bind _ ts)) =
    pPrintConnective undefined 0 "$false" "|" (map Literal ts)

instance Show Clause where
  show = prettyShow

instance Pretty Type where
  pPrint O = text "$o"
  pPrint ty = text . escapeAtom . show . tname $ ty

instance Show Type where
  show = prettyShow

instance Pretty FunType where
  pPrint FunType{args = args, res = res} =
    case args of
      [] -> pPrint res
      args -> pPrintTypes args <+> text ">" <+>
              pPrint res
    where
      pPrintTypes [arg] = pPrint arg
      pPrintTypes args =
        parens . hsep . punctuate (text " *") . map pPrint $ args

instance Show FunType where
  show = prettyShow

instance Pretty Name where
  pPrint = text . show

instance Show L.Token where
  show L.Atom{L.tokenName = x} = escapeAtom x
  show L.Defined{L.defined = x} = show x
  show L.Var{L.tokenName = x} = x
  show L.DistinctObject{L.tokenName = x} = quote '"' x
  show L.Number{L.value = x} = show x
  show L.Punct{L.kind = x} = show x
  show L.Eof = "end of file"
  show L.Error = "lexical error"

escapeAtom :: String -> String
escapeAtom s | not (null s') && isLower (head s') && all isNormal s' = s
             | otherwise = quote '\'' s
  where isNormal c = isAlphaNum c || c == '_'
        s' = dropWhile (== '$') s

quote :: Char -> String -> String
quote c s = [c] ++ concatMap escape s ++ [c]
  where escape c' | c == c' = ['\\', c]
        escape '\\' = "\\\\"
        escape c = [c]

instance Pretty Term where
  pPrint (Var (v ::: _)) =
    pPrint v
  pPrint ((f ::: _) :@: []) =
    case f of
      Fixed Integer{} -> text (show f)
      Fixed Rational{} -> text (show f)
      Fixed Real{} -> text (show f)
      _ -> text (escapeAtom (show f))
  pPrint ((f ::: _) :@: ts) =
    text (escapeAtom (show f)) <>
    parens (sep (punctuate comma (map pPrint ts)))

instance Show Term where
  show = prettyShow

instance Pretty Atomic where
  pPrint (t :=: u) = pPrint t <> text "=" <> pPrint u
  pPrint (Tru t) = pPrint t

instance Show Atomic where
  show = prettyShow

instance Pretty Form where
  pPrintPrec _ = pPrintTff

instance Show Form where
  show = prettyShow

pPrintFof, pPrintTff :: Rational -> Form -> Doc
pPrintFof = pPrintForm (\(x ::: _) -> pPrint x)
pPrintTff = pPrintForm (\(x ::: ty) -> pPrint x <> colon <+> pPrint ty)

pPrintForm :: (Variable -> Doc) -> Rational -> Form -> Doc
-- We use two precedences, the lowest for binary connectives
-- and the highest for everything else.
pPrintForm _bind _p (Literal (Pos (t :=: u))) =
  pPrint t <> text "=" <> pPrint u
pPrintForm _bind _p (Literal (Neg (t :=: u))) =
  pPrint t <> text "!=" <> pPrint u
pPrintForm _bind p (Literal (Pos t)) = pPrintPrec prettyNormal p t
pPrintForm bind p (Literal (Neg t)) = pPrintForm bind p (Not (Literal (Pos t)))
pPrintForm bind _p (Not f) = text "~" <> pPrintForm bind 1 f
pPrintForm bind p (And ts) = pPrintConnective bind p "$true" "&" ts
pPrintForm bind p (Or ts) = pPrintConnective bind p "$false" "|" ts
pPrintForm bind p (Equiv t u) = pPrintConnective bind p undefined "<=>" [t, u]
pPrintForm bind _p (ForAll (Bind vs f)) = pPrintQuant bind "!" vs f
pPrintForm bind _p (Exists (Bind vs f)) = pPrintQuant bind "?" vs f
pPrintForm bind p (Connective c t u) = pPrintConnective bind p (error "pPrint: Connective") (show c) [t, u]

instance Show Connective where
  show Implies = "=>"
  show Follows = "<="
  show Xor = "<~>"
  show Nor = "~|"
  show Nand = "~&"

pPrintConnective _bind _p ident _op [] = text ident
pPrintConnective bind p _ident _op [x] = pPrintForm bind p x
pPrintConnective bind p _ident op (x:xs) =
  maybeParens (p > 0) $
    sep (ppr x:[ nest 2 (text op <+> ppr x) | x <- xs ])
      where ppr = pPrintForm bind 1
            
pPrintQuant :: (Variable -> Doc) -> String -> Set.Set Variable -> Form -> Doc
pPrintQuant bind q vs f
  | Set.null vs = pPrintForm bind 1 f
  | otherwise =
    sep [
      text q <> brackets (sep (punctuate comma (map bind (Set.toList vs)))) <> colon,
      nest 2 (pPrintForm bind 1 f)]

instance Show Kind where
  show (Axiom kind) = kind
  show Conjecture = "conjecture"
  show Question = "question"

prettyNames :: Symbolic a => a -> a
prettyNames x0 = mapName replace x
  where
    replace name@Fixed{}  = name
    replace x@Unique{} = Map.findWithDefault (name (base x)) x sub

    sub = globalsScope `Map.union` pretty globalsUsed x

    pretty :: Symbolic a => Set String -> a -> Map Name Name
    pretty used x =
      case typeOf x of
        Bind_ -> bind used x
        _ -> collect (pretty used) x

    bind :: Symbolic a => Set String -> Bind a -> Map Name Name
    bind used (Bind vs x) =
      scope `Map.union` pretty used' x
      where
        (scope, used') = add used (map name (Set.toList vs))

    add used names =
      foldr add1 (Map.empty, used) names

    add1 (Fixed xs) (scope, used) =
      (scope, Set.insert (show xs) used)
    add1 x@(Unique _ base f) (scope, used) =
      (Map.insert x (name winner) scope,
       Set.insert winner (Set.fromList taken `Set.union` used))
      where
        cands = [f base n | n <- [0..]]
        Renaming taken winner =
          head [c | c@(Renaming xs x) <- cands,
                not (or [Set.member y used | y <- x:xs ])]

    globals =
      usort $
        [ f | f ::: _ <- functions x ] ++
        [ ty | Type ty _ _ <- types x ]
    (globalsScope, globalsUsed) = add fixed globals

    fixed = Set.fromList [ show xs | Fixed xs <- names x ]

    x = run x0 uniqueNames
