module NameMap(NameMap, lookup, lookup_, insert, member, delete, (!), fromList, toList, singleton) where

import Prelude hiding (lookup)
import Name
import Data.HashMap(Map)
import qualified Data.HashMap as Map
import Data.Int
import qualified Seq as S

type NameMap a = Map Int64 a

lookup :: Name -> NameMap a -> Maybe a
lookup x m = Map.lookup (uniqueId x) m

lookup_ :: Named a => a -> NameMap b -> b
lookup_ x m =
  case lookup (name x) m of
    Nothing -> error "NameMap.lookup_: key not found"
    Just y -> y

insert :: Named a => a -> NameMap a -> NameMap a
insert x m = Map.insert (uniqueId (name x)) x m

member :: Named a => a -> NameMap a -> Bool
member x m = keyMember (name x) m

keyMember :: Name -> NameMap a -> Bool
keyMember x m = Map.member (uniqueId x) m

delete :: Named a => a -> NameMap a -> NameMap a
delete x m = deleteKey (name x) m

deleteKey :: Name -> NameMap a -> NameMap a
deleteKey x m = Map.delete (uniqueId x) m

(!) :: NameMap a -> Name -> a
m ! x = m Map.! uniqueId (name x)

fromList :: (S.List f, Named a) => f a -> NameMap a
fromList xs = Map.fromList [ (uniqueId (name x), x) | x <- S.toList xs ]

toList :: NameMap a -> [a]
toList = Map.elems

singleton :: Named a => a -> NameMap a
singleton x = insert x Map.empty
