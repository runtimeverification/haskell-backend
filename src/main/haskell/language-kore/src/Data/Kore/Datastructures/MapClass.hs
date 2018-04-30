{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Datastructures.MapClass where

class Eq k => MapClass map k v where
    -- |'isEmpty' tells whether the map is empty
    isEmpty :: map k v -> Bool
    empty :: map k v
    lookup :: k -> map k v -> Maybe v
    insert :: k -> v -> map k v -> map k v
    delete :: k -> map k v -> map k v
