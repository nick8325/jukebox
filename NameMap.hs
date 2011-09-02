module NameMap(NameMap, insert, member, delete, (!), fromList, toList, singleton) where

import Name
import Data.HashMap(Map)
import qualified Data.HashMap as Map
import Data.Int
import qualified Seq as S

type NameMap a = Map Int64 a

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
