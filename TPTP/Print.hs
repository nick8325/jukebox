-- Pretty-printing of formulae. WARNING: icky code inside!
{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, TypeOperators, FlexibleInstances #-}
module TPTP.Print(prettyShow, chattyShow, prettyProblem, Level(..), Pretty)
       where

import qualified Data.ByteString.Char8 as BS
import Data.Char
import Text.PrettyPrint.HughesPJ
import qualified TPTP.Lexer as L
import Form
import Data.List
import qualified Data.HashMap as Map
import qualified Seq as S
import qualified NameMap
import NameMap(NameMap)
import Name

data Level = Normal | Chatty deriving (Eq, Ord)

class Pretty a where
  pPrint :: Int -> Level -> (Name -> BS.ByteString) -> a -> Doc

instance Pretty Name where
  pPrint _ _ env x = text (BS.unpack (env x))

pPrintSymbol :: Bool -> Int -> Level -> (Name -> BS.ByteString) -> Name ::: Type -> Doc
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
        [pPrint prec lev env (tname t)] ++
        [size (tmonotone t) | tmonotone t /= Infinite || tsize t /= Infinite] ++
        [size (tsize t) | tsize t /= Infinite]
    | otherwise = pPrint prec lev env (tname t)
    where size Infinite = empty
          size (Finite n) = int n

instance Show Type where
  show = chattyShow

instance Show L.Token where
  show L.Atom{L.name = x} = BS.unpack (escapeAtom x)
  show L.Defined{L.defined = x} = show x
  show L.Var{L.name = x} = BS.unpack x
  show L.DistinctObject{L.name = x} = BS.unpack (quote '"' x)
  show L.Number{L.value = x} = show x
  show L.Punct{L.kind = x} = show x

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
prettyProblem family l prob = vcat (map typeDecl (S.unique (types prob')) ++
                                    map funcDecl (S.unique (functions prob')) ++
                                    map (prettyInput family l env) prob')
    where typeDecl ty | name ty `elem` open stdNames = empty
                      | otherwise = typeClause ty (text "$tType")
          funcDecl (f ::: ty) | fof ty = empty
                              | otherwise = typeClause f (pPrint 0 l env ty)
          fof (FunType args res) = and [ name (typ arg) == nameI | arg <- args ] &&
                                   name res `elem` [nameI, nameO]
          typeClause name ty = prettyClause "tff" "type" "type"
                                      (pPrint 0 l env name <+> colon <+> ty)
          env = uniquify (S.unique (names prob'))
          prob' = open prob

prettyClause :: String -> String -> String -> Doc -> Doc
prettyClause family name kind rest =
  text family <> parens (sep [text name <> comma <+> text kind <> comma, rest]) <> text "."

instance (Symbolic a, Pretty a) => Show (Problem a) where
  show = render . prettyProblem "tff" Chatty

prettyInput :: Pretty a => String -> Level -> (Name -> BS.ByteString) -> Input a -> Doc
prettyInput family l env i = prettyClause family (BS.unpack (tag i)) (show (kind i)) (pPrint 0 l env (what i))

instance Pretty a => Pretty (Input a) where
  pPrint _ l env = prettyInput "tff" l env

instance Pretty a => Show (Input a) where
  show = chattyShow

instance Pretty Term where
  pPrint _ l env (Var v) = pPrintUse 0 l env v
  pPrint _ l env (f :@: []) = pPrintUse 0 l env f
  pPrint _ l env (f :@: ts) = pPrintUse 0 l env f <> pPrint 0 l env ts
  
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
  pPrint p l env (And ts) = prettyConnective l p env "$true" "&" (S.toList ts)
  pPrint p l env (Or ts) = prettyConnective l p env "$false" "|" (S.toList ts)
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

prettyQuant l env q vs f =
  sep [text q <> brackets (sep (punctuate comma (map (pPrintBinding 0 l env) (Map.elems vs)))) <> colon,
       nest 2 (pPrint 1 l env f)]

instance Show Kind where
  show Axiom = "axiom"
  show Conjecture = "conjecture"
  show Question = "question"

prettyShow, chattyShow :: Pretty a => a -> String
prettyShow = render . pPrint 0 Normal base
chattyShow = render . pPrint 0 Chatty (BS.pack . show)
