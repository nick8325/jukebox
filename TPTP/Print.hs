-- Pretty-printing of formulae.
{-# LANGUAGE FlexibleContexts, TypeSynonymInstances #-}
module TPTP.Print(prettyShow, chattyShow, reallyChattyShow,
                  prettyNormal, prettyChatty, prettyReallyChatty,
                  showPredType, showFunType, showArgs, prettyFunc,
                  prettyProblem, prettyInput)
                  where

import qualified Data.ByteString.Char8 as BS
import Data.Char
import Data.Ratio
import Text.PrettyPrint.HughesPJ
import Text.PrettyPrint.HughesPJClass
import qualified TPTP.Lexer as L
import Formula
import Data.List
import qualified Data.HashMap as Map
import qualified Data.Set as Set
import qualified AppList

class Pretty a => PrettyBinding a where
  pPrintBinding :: PrettyLevel -> Rational -> Variable a -> Doc

instance PrettyBinding Name where
  pPrintBinding l p v
    | l < prettyChatty && tname (vtype v) == BS.pack "$i" = 
      pPrintPrec l p (vname v)
    | otherwise = pPrintPrec l p v

instance Pretty BS.ByteString where
  pPrint = text . BS.unpack

instance Pretty L.Token where
  pPrint L.Atom{L.name = name} = pPrint (escapeAtom name)
  pPrint L.Defined{L.defined = defined} = text (show defined)
  pPrint L.Var{L.name = name} = pPrint name
  pPrint L.DistinctObject{L.name = name} = pPrint (quote '"' name)
  pPrint L.Number{L.value = x} = pPrint x
  pPrint L.Punct{L.kind = kind} = quotes (text (show kind))

escapeAtom :: BS.ByteString -> BS.ByteString
escapeAtom s | not (BS.null s') && isLower (BS.head s') && BS.all isNormal s' = s
             | otherwise = quote '\'' s
  where isNormal c = isAlphaNum c || c == '_'
        s' = BS.dropWhile (== '$') s

quote :: Char -> BS.ByteString -> BS.ByteString
quote c s = BS.concat [BS.pack [c], BS.concatMap escape s, BS.pack [c]]
  where escape c' | c == c' = BS.pack ['\\', c]
        escape '\\' = BS.pack "\\\\"
        escape c = BS.singleton c

instance Pretty a => Pretty (Type a) where
  pPrintPrec l p t | l >= prettyReallyChatty = 
                     hcat (punctuate (text "/")
                           [pPrint (tname t),
                            size (tmonotone t),
                            size (tsize t)])
                   | otherwise = pPrint (tname t)
    where size Infinite = empty
          size (Finite n) = pPrint n

instance Pretty a => Pretty (Function a) where
  pPrintPrec l p f = pPrintName l p (escapeAtom (BS.pack (render (pPrintPrec l p (fname f))))) (fres f)
instance Pretty a => Pretty (Predicate a) where
  pPrintPrec l pr p = pPrint (escapeAtom (BS.pack (render (pPrintPrec l pr (pname p)))))
instance Pretty a => Pretty (Variable a) where
  pPrintPrec l p v = pPrintName l p (BS.pack (render (pPrintPrec l p (vname v)))) (vtype v)

instance Pretty a => Show (Function a) where show = chattyShow
instance Pretty a => Show (Predicate a) where show = chattyShow
instance Pretty a => Show (Variable a) where show = chattyShow

pPrintName :: Pretty a => PrettyLevel -> Rational -> Name -> Type a -> Doc
pPrintName l _ name ty
  | l >= prettyChatty = text (BS.unpack name) <> colon <> pPrintPrec l 0 ty
  | otherwise = text (BS.unpack name)

showPredType args = showFunType args (Type (BS.pack "$o") Infinite Infinite)
showFunType [] res = prettyShow res
showFunType [arg] res = prettyShow arg ++ " > " ++ prettyShow res
showFunType args res = "(" ++ showArgs args ++ ") > " ++ prettyShow res
showArgs tys = intercalate " * " (map prettyShow tys)

prettyProblem :: (Pretty a, Pretty (f a)) => String -> PrettyLevel -> Problem f a -> Doc
prettyProblem family l prob = vcat (map typeDecl (Map.elems (types prob)) ++
                              map predDecl (Map.elems (preds prob)) ++
                              map funDecl (Map.elems (funs prob)) ++
                              map (prettyInput family l) (inputs prob))
    where typeDecl ty = typeClause (pPrintPrec l 0 ty) (text "$tType")
          predDecl (args, p) = typeClause (pPrint (pname p)) (text (showPredType args))
          funDecl (args, f) = typeClause (pPrint (fname f)) (text (showFunType args (fres f)))
          typeClause name ty = prettyClause "tff" "type" "type"
                                      (name <+> colon <+> ty)

prettyClause :: String -> String -> String -> Doc -> Doc
prettyClause family name kind rest =
  text family <> parens (sep [text name <> comma <+> text kind <> comma, rest]) <> text "."

instance (Pretty a, Pretty (f a)) => Pretty (Problem f a) where
  pPrintPrec l _ = prettyProblem "tff" l

instance (Pretty a, Pretty (f a)) => Show (Problem f a) where
  show = chattyShow

prettyInput :: Pretty a => String -> PrettyLevel -> Input a -> Doc
prettyInput family l i = prettyClause family (BS.unpack (tag i)) (show (kind i)) (pPrintPrec l 0 (formula i))

instance Pretty a => Pretty (Input a) where
  pPrintPrec l _ = prettyInput "tff" l

instance Pretty a => Show (Input a) where
  show = chattyShow

instance Pretty a => Pretty (Term a) where
  pPrintPrec l _ (Var v) = pPrintPrec l 0 v
  pPrintPrec l _ (f :@: ts) = prettyFunc l (pPrintPrec l 0 f) ts

prettyFunc :: Pretty a => PrettyLevel -> Doc -> [Term a] -> Doc
prettyFunc l d [] = d
prettyFunc l d ts = d <> parens (sep (punctuate comma (map (pPrintPrec l 0) ts))) 

instance Pretty a => Show (Term a) where
  show = chattyShow

instance Pretty a => Pretty (Atom a) where
  pPrintPrec l _ (t :=: u) = pPrintPrec l 0 t <> text "=" <> pPrintPrec l 0 u
  pPrintPrec l _ (p :?: ts) = prettyFunc l (pPrintPrec l 0 p) ts

instance Pretty a => Show (Atom a) where
  show = chattyShow

instance (Pretty a, PrettyBinding a) => Pretty (Formula a) where
  -- We use two precedences, the lowest for binary connectives
  -- and the highest for everything else.
  pPrintPrec l p (Literal (Neg (t :=: u))) =
    pPrintPrec l 0 t <> text "!=" <> pPrintPrec l 0 u
  pPrintPrec l p (Literal (Neg t)) = pPrintPrec l p (Not (Literal (Pos t)))
  pPrintPrec l p (Literal (Pos t)) = pPrintPrec l p t
  pPrintPrec l p (Not f) = text "~" <> pPrintPrec l 1 f
  pPrintPrec l p (And ts) = prettyConnective l p "$true" "&" (AppList.toList ts)
  pPrintPrec l p (Or ts) = prettyConnective l p "$false" "|" (AppList.toList ts)
  pPrintPrec l p (Equiv t u) = prettyConnective l p undefined "<=>" [t, u]
  pPrintPrec l p (ForAll vs f) = prettyQuant l "!" vs f
  pPrintPrec l p (Exists vs f) = prettyQuant l "?" vs f

prettyConnective l p ident op [] = text ident
prettyConnective l p ident op [x] = pPrintPrec l p x
prettyConnective l p ident op (x:xs) =
  prettyParen (p > 0) $
    sep (ppr x:[ nest 2 (text op <+> ppr x) | x <- xs ])
      where ppr = pPrintPrec l 1

prettyQuant l q vs f =
  sep [text q <> brackets (sep (punctuate comma (map (pPrintBinding l 0) (Set.toList vs)))) <> colon,
       nest 2 (pPrintPrec l 1 f)]

instance Show Kind where
  show Axiom = "axiom"
  show NegatedConjecture = "negated_conjecture"

prettyChatty, prettyReallyChatty :: PrettyLevel
prettyChatty = PrettyLevel 1
prettyReallyChatty = PrettyLevel 2

chattyShow :: Pretty a => a -> String
chattyShow = render . pPrintPrec prettyChatty 0

reallyChattyShow :: Pretty a => a -> String
reallyChattyShow = render . pPrintPrec prettyReallyChatty 0
