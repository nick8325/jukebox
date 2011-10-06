module ParadoxParser.Convert where

import qualified Form as New
import qualified ParadoxParser.Form as Old
import qualified Seq
import Data.List
import ParadoxParser.Name hiding (name)
import ParadoxParser.Str
import qualified NameMap
import qualified Name
import qualified Data.ByteString.Char8 as BS

form :: New.Form -> Old.Form
form (New.Literal (New.Pos l)) = Old.Atom (atom l)
form (New.Literal (New.Neg l)) = Old.Not (Old.Atom (atom l))
form (New.Not f) = Old.Not (form f)
form (New.And fs) = Old.And (map form (Seq.toList fs))
form (New.Or fs) = Old.Or (map form (Seq.toList fs))
form (New.Equiv f g) = Old.Equiv (form f) (form g)
form (New.Connective New.Implies f g) = Old.Imp (form f) (form g)
form (New.Connective New.Follows f g) = Old.Foll (form f) (form g)
form (New.Connective New.Xor f g) = Old.Xor (form f) (form g)
form (New.Connective New.Nor f g) = Old.Nor (form f) (form g)
form (New.Connective New.Nand f g) = Old.Nand (form f) (form g)
form (New.ForAll b) = Old.ForAll (bind b)
form (New.Exists b) = Old.Exists (bind b)

bind :: New.Bind New.Form -> Old.Bind Old.Form
bind (New.Bind vs f) = Old.Bind (sort (map var (NameMap.toList vs))) (form f)

atom :: New.Atomic -> Old.Atom
atom (t New.:=: u) = term t Old.:=: term u
atom (New.Tru p) = term p Old.:=: Old.truth

term (New.Var v) = Old.Var (var v)
term (f New.:@: xs) = Old.Fun (fun f) (map term xs)

var v = name v Old.::: Old.V Old.top
fun (f Name.::: New.FunType args res) = name f Old.::: (replicate (length args) Old.top Old.:-> res')
  where res' | res == New.O = Old.bool
             | otherwise = Old.top
name n = Name (bstr (Name.baseName (Name.name n)))

input :: New.Input New.Form -> Old.Input Old.Form
input (New.Input tag kind what) = Old.Input kind' (BS.unpack tag) (form what)
  where kind' =
          case kind of
            New.Conjecture -> Old.Conjecture
            New.Axiom -> Old.Axiom