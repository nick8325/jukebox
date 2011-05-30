-- Pretty-printing of formulae.
module TPTP.Print(prettyShow, chattyShow, reallyChattyShow,
                  prettyNormal, prettyChatty, prettyReallyChatty,
                  showPredType, showFunType, showArgs,
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
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified AppList

instance Pretty BS.ByteString where
  pPrint = text . BS.unpack

instance Pretty L.Token where
  pPrint L.Atom{L.name = name} = pPrint (escapeAtom name)
  pPrint L.Defined{L.defined = defined} = text (show defined)
  pPrint L.Var{L.name = name} = pPrint name
  pPrint L.DistinctObject{L.name = name} = pPrint name
  pPrint L.Number{L.value = x} = pPrint x
  pPrint L.Punct{L.kind = kind} = text (show kind)

escapeAtom :: BS.ByteString -> BS.ByteString
escapeAtom s | not (BS.null s') && isLower (BS.head s') && BS.all isNormal s' = s
             | otherwise = BS.concat [BS.pack "'", BS.concatMap escape s, BS.pack "'"]
  where isNormal c = isAlphaNum c || c == '_'
        s' = BS.dropWhile (== '$') s
        escape '\'' = BS.pack "\\'"
        escape '\\' = BS.pack "\\\\"
        escape c = BS.singleton c

instance Pretty Type where
  pPrintPrec l p t | l >= prettyReallyChatty = 
                     hcat (punctuate (text "/")
                           [pPrint (tname t),
                            size (tmonotone t),
                            size (tsize t)])
                   | otherwise = pPrint (tname t)
    where size Infinite = empty
          size (Finite n) = pPrint n

instance Pretty Function where
  pPrintPrec l p f = pPrintName l p (escapeAtom (fname f)) (fres f)
instance Show Predicate where
  show = BS.unpack . escapeAtom . pname
instance Pretty Variable where
  pPrintPrec l p v = pPrintName l p (vname v) (vtype v)
pPrintBinding :: PrettyLevel -> Variable -> Doc
pPrintBinding l v | tname (vtype v) == BS.pack "$i" = pPrintPrec l 0 v
                  | otherwise = pPrintPrec (l `max` prettyChatty) 0 v

instance Show Function where show = chattyShow
instance Show Variable where show = chattyShow

pPrintName :: PrettyLevel -> Rational -> BS.ByteString -> Type -> Doc
pPrintName l _ name ty
  | l >= prettyChatty = text (BS.unpack name) <> colon <> pPrintPrec l 0 ty
  | otherwise = text (BS.unpack name)

showPredType args = showFunType args (Type (BS.pack "$o") Infinite Infinite)
showFunType [] res = prettyShow res
showFunType [arg] res = prettyShow arg ++ " > " ++ prettyShow res
showFunType args res = "(" ++ showArgs args ++ ") > " ++ prettyShow res
showArgs tys = intercalate " * " (map prettyShow tys)

prettyProblem :: Pretty a => String -> PrettyLevel -> Problem a -> Doc
prettyProblem family l prob = vcat (map typeDecl (Map.elems (types prob)) ++
                              map predDecl (Map.elems (preds prob)) ++
                              map funDecl  (Map.elems (funs prob)) ++
                              map (prettyInput family l) (inputs prob))
    where typeDecl ty = typeClause (pPrintPrec l 0 ty) (text "$tType")
          predDecl (args, p) = typeClause (pPrint (pname p)) (text (showPredType args))
          funDecl (args, f) = typeClause (pPrint (fname f)) (text (showFunType args (fres f)))
          typeClause name ty = prettyClause "tff" "type" "type"
                                      (name <+> colon <+> ty)

prettyClause :: String -> String -> String -> Doc -> Doc
prettyClause family name kind rest =
  text family <> parens (sep [text name <> comma <+> text kind <> comma, rest]) <> text "."

instance Pretty a => Pretty (Problem a) where
  pPrintPrec l _ = prettyProblem "tff" l

instance Pretty a => Show (Problem a) where
  show = chattyShow

prettyInput :: Pretty a => String -> PrettyLevel -> Input a -> Doc
prettyInput family l i = prettyClause family (BS.unpack (tag i)) (show (kind i)) (pPrintPrec l 0 (formula i))

instance Pretty a => Pretty (Input a) where
  pPrintPrec l _ = prettyInput "tff" l

instance Pretty a => Show (Input a) where
  show = chattyShow

instance Pretty Term where
  pPrintPrec l _ (Var v) = pPrintPrec l 0 v
  pPrintPrec l _ (f :@: ts) = prettyFunc l (pPrintPrec l 0 f) ts

prettyFunc :: PrettyLevel -> Doc -> [Term] -> Doc
prettyFunc l d [] = d
prettyFunc l d ts = d <> parens (sep (punctuate comma (map (pPrintPrec l 0) ts))) 

instance Show Term where
  show = chattyShow

instance Pretty Atom where
  pPrintPrec l _ (t :=: u) = pPrintPrec l 0 t <> text "=" <> pPrintPrec l 0 u
  pPrintPrec l _ (p :?: ts) = prettyFunc l (text (show p)) ts

instance Show Atom where
  show = chattyShow

instance Pretty Formula where
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
  sep [text q <> brackets (sep (punctuate comma (map (pPrintBinding l) (Set.toList vs)))) <> colon,
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
