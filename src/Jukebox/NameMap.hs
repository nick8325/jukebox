module Jukebox.NameMap(NameMap, empty, lookup, lookup_, insert, member, delete, (!), fromList, toList, singleton, null, union, intersection) where

import Prelude hiding (lookup)
import Jukebox.Name
import Data.IntMap(IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Int

type NameMap a = IntMap a

empty :: NameMap a
empty = IntMap.empty

lookup :: Name -> NameMap a -> Maybe a
lookup x m = IntMap.lookup (uniqueId x) m

lookup_ :: Named a => a -> NameMap b -> b
lookup_ x m =
  case lookup (name x) m of
    Nothing -> error "NameMap.lookup_: key not found"
    Just y -> y

insert :: Named a => a -> NameMap a -> NameMap a
insert x m = IntMap.insert (uniqueId (name x)) x m

member :: Named a => a -> NameMap a -> Bool
member x m = keyMember (name x) m

keyMember :: Name -> NameMap a -> Bool
keyMember x m = IntMap.member (uniqueId x) m

delete :: Named a => a -> NameMap a -> NameMap a
delete x m = deleteKey (name x) m

deleteKey :: Name -> NameMap a -> NameMap a
deleteKey x m = IntMap.delete (uniqueId x) m

(!) :: NameMap a -> Name -> a
m ! x = m IntMap.! uniqueId (name x)

fromList :: Named a => [a] -> NameMap a
fromList xs = IntMap.fromList [ (uniqueId (name x), x) | x <- xs ]

toList :: NameMap a -> [a]
toList = IntMap.elems

singleton :: Named a => a -> NameMap a
singleton x = insert x IntMap.empty

union :: NameMap a -> NameMap a -> NameMap a
union = IntMap.union

intersection :: NameMap a -> NameMap a -> NameMap a
intersection = IntMap.intersection
