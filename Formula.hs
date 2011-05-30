module Formula where

import AppList(AppList)
import qualified AppList
import qualified Data.Set
import Data.Set(Set)
import Data.Map(Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Ord
import qualified Data.ByteString.Char8 as BS
import Data.List
import Data.Ratio
import Text.PrettyPrint.HughesPJ
import Text.PrettyPrint.HughesPJClass

type Name = BS.ByteString -- for now
type Tag = BS.ByteString

data DomainSize = Finite !Int | Infinite deriving (Eq, Ord) 

data Type = Type
  { tname :: !Name,
    -- type is monotone when domain size is >= tmonotone
    tmonotone :: !DomainSize,
    -- if there is a model of size >= tsize then there is a model of size tsize
    tsize :: !DomainSize }

instance Eq Type where
  t1 == t2 = tname t1 == tname t2

instance Ord Type where
  compare = comparing tname

instance Show Type where
  show = BS.unpack . tname

data Function = Function { fname :: !Name, fres :: !Type }
data Predicate = Predicate { pname :: !Name }
data Variable = Variable { vname :: !Name, vtype :: !Type } deriving (Eq, Ord)

instance Pretty Function where
  pPrintPrec l p f = pPrintName l p (fname f) (fres f)
instance Show Predicate where
  show = BS.unpack . pname
instance Pretty Variable where
  pPrintPrec l p v = pPrintName l p (vname v) (vtype v)
instance Show Function where show = chattyShow
instance Show Variable where show = chattyShow

pPrintName :: PrettyLevel -> Rational -> BS.ByteString -> Type -> Doc
pPrintName l _ name ty
  | l >= prettyChatty = text (BS.unpack name) <> colon <> text (show ty)
  | otherwise = text (BS.unpack name)

showPredType args = showFunType args (Type (BS.pack "$o") Infinite Infinite)
showFunType [] res = show res
showFunType [arg] res = show arg ++ " > " ++ show res
showFunType args res = "(" ++ showArgs args ++ ") > " ++ show res
showArgs tys = intercalate " * " (map show tys)

data Problem a = Problem
  { types :: Map BS.ByteString Type,
    preds :: Map BS.ByteString ([Type], Predicate),
    funs :: Map BS.ByteString ([Type], Function),
    inputs :: [Input a] }

prettyProblem :: Pretty a => String -> PrettyLevel -> Problem a -> Doc
prettyProblem family l prob = vcat (map typeDecl (Map.elems (types prob)) ++
                              map predDecl (Map.elems (preds prob)) ++
                              map funDecl  (Map.elems (funs prob)) ++
                              map (prettyInput family l) (inputs prob))
    where typeDecl ty =
            typeClause (tname ty) (text "$tType") <+>
              hsep ([ text "%" | tmonotone ty /= Infinite || tsize ty /= Infinite ] ++
                    [ text (intercalate ", "
                      ([ "monotone above size " ++ show x | Finite x <- [tmonotone ty] ] ++
                       [ "maximum size is " ++ show x | Finite x <- [tsize ty] ]))])
          predDecl (args, p) = typeClause (pname p) (text (showPredType args))
          funDecl (args, f) = typeClause (fname f) (text (showFunType args (fres f)))
          typeClause name ty = prettyClause "tff" "type" "type"
                                      (text (BS.unpack name) <+> colon <+> ty)

prettyClause :: String -> String -> String -> Doc -> Doc
prettyClause family name kind rest =
  text family <> parens (sep [text name <> comma <+> text kind <> comma, rest]) <> text "."

instance Pretty a => Pretty (Problem a) where
  pPrintPrec l _ = prettyProblem "tff" l

instance Pretty a => Show (Problem a) where
  show = chattyShow

data Input a = Input
  { tag :: !Tag,
    kind :: !Kind,
    formula :: !a }

prettyInput :: Pretty a => String -> PrettyLevel -> Input a -> Doc
prettyInput family l i = prettyClause family (BS.unpack (tag i)) (show (kind i)) (pPrintPrec l 0 (formula i))

instance Pretty a => Pretty (Input a) where
  pPrintPrec l _ = prettyInput "tff" l

instance Pretty a => Show (Input a) where
  show = chattyShow

instance Functor Input where
  fmap f x = x { formula = f (formula x) }

data Term = Var !Variable | !Function :@: [Term]

instance Pretty Term where
  pPrintPrec l _ (Var v) = pPrintPrec l 0 v
  pPrintPrec l _ (f :@: ts) = prettyFunc l (pPrintPrec l 0 f) ts

prettyFunc :: PrettyLevel -> Doc -> [Term] -> Doc
prettyFunc l d [] = d
prettyFunc l d ts = d <> parens (sep (punctuate comma (map (pPrintPrec l 0) ts))) 

instance Show Term where
  show = chattyShow

ty :: Term -> Type
ty (Var Variable{vtype = ty}) = ty
ty (Function{fres = ty} :@: _) = ty

data Atom = Term :=: Term | !Predicate :?: [Term]

instance Pretty Atom where
  pPrintPrec l _ (t :=: u) = pPrintPrec l 0 t <> text "=" <> pPrintPrec l 0 u
  pPrintPrec l _ (p :?: ts) = prettyFunc l (text (show p)) ts

instance Show Atom where
  show = chattyShow

data Signed a = Pos !a | Neg !a deriving Show
type Literal = Signed Atom

data Formula
  = Literal !Literal
  | Not !Formula
  | And !(AppList Formula)
  | Or !(AppList Formula)
  | Equiv !Formula !Formula
  | ForAll !(Set Variable) !Formula
  | Exists !(Set Variable) !Formula

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
  sep [text q <> brackets (sep (punctuate comma (map (pPrintPrec l 0) (Set.toList vs)))) <> colon,
       nest 2 (pPrintPrec l 1 f)]

data CNF = CNF [Clause]
data Clause = Clause !(Set Variable) [Literal]

neg :: Signed a -> Signed a
neg (Pos x) = Neg x
neg (Neg x) = Pos x

data Kind = Axiom | NegatedConjecture deriving (Eq, Ord)

instance Show Kind where
  show Axiom = "axiom"
  show NegatedConjecture = "negated_conjecture"

-- Nowhere better to put this
prettyChatty :: PrettyLevel
prettyChatty = PrettyLevel 1

chattyShow :: Pretty a => a -> String
chattyShow = render . pPrintPrec prettyChatty 0
