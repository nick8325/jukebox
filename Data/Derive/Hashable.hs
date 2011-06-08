module Data.Derive.Hashable where

{-
import "hashable" Data.Hashable

example :: Sample

instance Hashable alpha => Hashable (Sample alpha) where
  hashWithSalt s x =
    let variant n s = if length [First{}, Second{}, Third{}] > 1 then s `combine` n else s in
    case x of
      First -> variant 0 s
      Second x1 x2 -> variant 1 s `hashWithSalt` x1 `hashWithSalt` x2
      Third x1 -> variant 2 s `hashWithSalt` x1
-}

-- GENERATED START

import Data.Derive.DSL.DSL
import Data.Derive.Internal.Derivation

makeHashable :: Derivation
makeHashable = derivationDSL "Hashable" dslHashable

dslHashable =
    List [Instance ["Hashable"] "Hashable" (List [App "InsDecl" (List
    [App "FunBind" (List [List [App "Match" (List [App "Ident" (List [
    String "hashWithSalt"]),List [App "PVar" (List [App "Ident" (List
    [String "s"])]),App "PVar" (List [App "Ident" (List [String "x"])]
    )],App "Nothing" (List []),App "UnGuardedRhs" (List [App "Let" (
    List [App "BDecls" (List [List [App "FunBind" (List [List [App
    "Match" (List [App "Ident" (List [String "variant"]),List [App
    "PVar" (List [App "Ident" (List [String "n"])]),App "PVar" (List [
    App "Ident" (List [String "s"])])],App "Nothing" (List []),App
    "UnGuardedRhs" (List [App "If" (List [App "InfixApp" (List [App
    "App" (List [App "Var" (List [App "UnQual" (List [App "Ident" (
    List [String "length"])])]),App "List" (List [MapCtor (App
    "RecConstr" (List [App "UnQual" (List [App "Ident" (List [CtorName
    ])]),List []]))])]),App "QVarOp" (List [App "UnQual" (List [App
    "Symbol" (List [String ">"])])]),App "Lit" (List [App "Int" (List
    [Int 1])])]),App "InfixApp" (List [App "Var" (List [App "UnQual" (
    List [App "Ident" (List [String "s"])])]),App "QVarOp" (List [App
    "UnQual" (List [App "Ident" (List [String "combine"])])]),App
    "Var" (List [App "UnQual" (List [App "Ident" (List [String "n"])])
    ])]),App "Var" (List [App "UnQual" (List [App "Ident" (List [
    String "s"])])])])]),App "BDecls" (List [List []])])]])]]),App
    "Case" (List [App "Var" (List [App "UnQual" (List [App "Ident" (
    List [String "x"])])]),MapCtor (App "Alt" (List [App "PApp" (List
    [App "UnQual" (List [App "Ident" (List [CtorName])]),MapField (App
    "PVar" (List [App "Ident" (List [Concat (List [String "x",ShowInt
    FieldIndex])])]))]),App "UnGuardedAlt" (List [Fold (App "InfixApp"
    (List [Tail,App "QVarOp" (List [App "UnQual" (List [App "Ident" (
    List [String "hashWithSalt"])])]),Head])) (Concat (List [Reverse (
    MapField (App "Var" (List [App "UnQual" (List [App "Ident" (List [
    Concat (List [String "x",ShowInt FieldIndex])])])]))),List [
    Application (List [App "Var" (List [App "UnQual" (List [App
    "Ident" (List [String "variant"])])]),App "Lit" (List [App "Int" (
    List [CtorIndex])]),App "Var" (List [App "UnQual" (List [App
    "Ident" (List [String "s"])])])])]]))]),App "BDecls" (List [List [
    ]])]))])])]),App "BDecls" (List [List []])])]])])])]
-- GENERATED STOP
