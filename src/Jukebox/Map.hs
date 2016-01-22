{-# LANGUAGE NoMonomorphismRestriction #-}
module Jukebox.Map where

import qualified Data.Map.Lazy as H

type Map a b = H.Map a b

fromList = H.fromList
toList = H.toList
insertWith = H.insertWith
empty = H.empty
findWithDefault = H.findWithDefault
lookup = H.lookup
insert = H.insert
delete = H.delete
elems = H.elems
union = H.union
intersection = H.intersection
null = H.null
m ! x = findWithDefault (error "Map.!: key not found") x m

member x m =
  case H.lookup x m of
    Nothing -> False
    Just{} -> True

m1 \\ m2 =
  H.foldrWithKey (\k v m -> H.delete k m) m1 m2
