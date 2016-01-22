-- Pretty-printing of formulae. WARNING: icky code inside!
{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, TypeOperators, FlexibleInstances #-}
module Jukebox.TPTP.Print(prettyShow, chattyShow, prettyFormula, prettyProblem, Level(..), Pretty)
       where

import Data.Char
import Text.PrettyPrint.HughesPJ
import qualified Jukebox.TPTP.Lexer as L
import Jukebox.Form
import Data.List
import qualified Jukebox.Map as Map
import qualified Jukebox.NameMap as NameMap
import Jukebox.NameMap(NameMap)
import Jukebox.Name
import Jukebox.Utils

data Level = Normal | Chatty deriving (Eq, Ord)

class Pretty a where
  pPrint :: Int -> Level -> (Name -> String) -> a -> Doc

instance Pretty Name where
  pPrint _ _ env x = text (env x)

pPrintSymbol :: Bool -> Int -> Level -> (Name -> String) -> Name ::: Type -> Doc
pPrintSymbol full prec lev env (x ::: t)
  | full || lev >= Chatty = pPrint prec lev env x <> colon <> pPrint prec lev env t
  | otherwise = pPrint prec lev env x

pPrintBinding prec lev env (x ::: t) =
  pPrintSymbol (name t /= nameI) prec lev env (x ::: typ t)

pPrintUse prec lev env (x ::: t) =
  pPrintSymbol False prec lev env (x ::: typ t)

instance Pretty Type where
  pPrint prec lev env O = pPrint prec lev env nameO
  pPrint prec lev env t
    | lev >= Chatty = 
      hcat . punctuate (text "/") $
        [text (escapeAtom (env (tname t)))] ++
        [size (tmonotone t) | tmonotone t /= Infinite || tsize t /= Infinite] ++
        [size (tsize t) | tsize t /= Infinite]
    | otherwise = text (escapeAtom (env (tname t)))
    where size Infinite = empty
          size (Finite n) = int n

instance Show Type where
  show = chattyShow

instance Show L.Token where
  show L.Atom{L.name = x} = escapeAtom x
  show L.Defined{L.defined = x} = show x
  show L.Var{L.name = x} = x
  show L.DistinctObject{L.name = x} = quote '"' x
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

instance Pretty FunType where
  pPrint prec lev env FunType{args = args, res = res} =
    case args of
      [] -> pPrint prec lev env res
      args -> pPrint prec lev env args <+> text ">" <+>
              pPrint prec lev env res

instance Show FunType where
  show = chattyShow

instance Pretty [Type] where
  pPrint prec lev env [arg] = pPrint prec lev env arg
  pPrint prec lev env args =
    parens (hsep (intersperse (text "*")
                  (map (pPrint 0 lev env) args)))

prettyProblem :: (Symbolic a, Pretty a) => String -> Level -> Problem a -> Doc
prettyProblem family l prob = vcat (map typeDecl (usort (types prob')) ++
                                    map funcDecl (usort (functions prob')) ++
                                    map (prettyInput family l env) prob')
    where typeDecl ty | name ty `elem` open stdNames || isFof prob' = empty
                      | otherwise = typeClause ty (text "$tType")
          funcDecl (f ::: ty) | isFof prob' = empty
                              | otherwise = typeClause f (pPrint 0 l (escapeAtom . env) ty)
          typeClause name ty = prettyClause "tff" "type" "type"
                                      (pPrint 0 l (escapeAtom . env) name <+> colon <+> ty)
          env = uniquify (usort (names prob'))
          prob' = open prob

prettyClause :: String -> String -> String -> Doc -> Doc
prettyClause family name kind rest =
  text family <> parens (sep [text name <> comma <+> text kind <> comma, rest]) <> text "."

instance (Symbolic a, Pretty a) => Show (Problem a) where
  show = render . prettyProblem "tff" Chatty

prettyInput :: Pretty a => String -> Level -> (Name -> String) -> Input a -> Doc
prettyInput family l env i = prettyClause family (tag i) (show (kind i)) (pPrint 0 l env (what i))

instance Pretty a => Pretty (Input a) where
  pPrint _ l env = prettyInput "tff" l env

instance Pretty a => Show (Input a) where
  show = chattyShow

instance Pretty Term where
  pPrint _ l env (Var v) = pPrintUse 0 l env v
  pPrint _ l env (f :@: []) = pPrintUse 0 l (escapeAtom . env) f
  pPrint _ l env (f :@: ts) = pPrintUse 0 l (escapeAtom . env) f <> pPrint 0 l env ts
  
instance Pretty [Term] where
  pPrint _ l env ts = parens (sep (punctuate comma (map (pPrint 0 l env) ts)))

instance Show Term where
  show = chattyShow

instance Pretty Atomic where
  pPrint _ l env (t :=: u) = pPrint 0 l env t <> text "=" <> pPrint 0 l env u
  pPrint _ l env (Tru t) = pPrint 0 l env t

instance Show Atomic where
  show = chattyShow

instance Pretty Clause where
  pPrint p l env c@(Clause (Bind vs ts))
    | and [ name (typ v) == nameI | v <- NameMap.toList vs ] =
       prettyConnective l p env "$false" "|" (map Literal ts)
    | otherwise =
       pPrint p l env (toForm c)

instance Show Clause where
  show = chattyShow

instance Pretty Form where
  -- We use two precedences, the lowest for binary connectives
  -- and the highest for everything else.
  pPrint p l env (Literal (Pos (t :=: u))) =
    pPrint 0 l env t <> text "=" <> pPrint 0 l env u
  pPrint p l env (Literal (Neg (t :=: u))) =
    pPrint 0 l env t <> text "!=" <> pPrint 0 l env u
  pPrint p l env (Literal (Pos t)) = pPrint p l env t
  pPrint p l env (Literal (Neg t)) = pPrint p l env (Not (Literal (Pos t)))
  pPrint p l env (Not f) = text "~" <> pPrint 1 l env f
  pPrint p l env (And ts) = prettyConnective l p env "$true" "&" ts
  pPrint p l env (Or ts) = prettyConnective l p env "$false" "|" ts
  pPrint p l env (Equiv t u) = prettyConnective l p env undefined "<=>" [t, u]
  pPrint p l env (ForAll (Bind vs f)) = prettyQuant l env "!" vs f
  pPrint p l env (Exists (Bind vs f)) = prettyQuant l env "?" vs f
  pPrint p l env (Connective c t u) = prettyConnective l p env (error "pPrint: Connective") (show c) [t, u]

instance Show Form where
  show = chattyShow

instance Show Connective where
  show Implies = "=>"
  show Follows = "<="
  show Xor = "<~>"
  show Nor = "~|"
  show Nand = "~&"

prettyConnective l p env ident op [] = text ident
prettyConnective l p env ident op [x] = pPrint p l env x
prettyConnective l p env ident op (x:xs) =
  prettyParen (p > 0) $
    sep (ppr x:[ nest 2 (text op <+> ppr x) | x <- xs ])
      where ppr = pPrint 1 l env
            
prettyParen False = id
prettyParen True = parens

prettyQuant l env q vs f | Map.null vs = pPrint 1 l env f
prettyQuant l env q vs f =
  sep [text q <> brackets (sep (punctuate comma (map (pPrintBinding 0 l env) (Map.elems vs)))) <> colon,
       nest 2 (pPrint 1 l env f)]

instance Show Kind where
  show Axiom = "axiom"
  show Conjecture = "conjecture"
  show Question = "question"

prettyShow, chattyShow :: Pretty a => a -> String
prettyShow = render . pPrint 0 Normal base
chattyShow = render . pPrint 0 Chatty show

prettyFormula :: (Pretty a, Symbolic a) => a -> String
prettyFormula prob = render . pPrint 0 Normal env $ prob
  where env = uniquify (usort (names prob))
