{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
module Data.Kore.Datastructures.MapClass where

class Eq k => MapClass map k v | map -> k, map -> v where
    -- |'isEmpty' tells whether the map is empty
    isEmpty :: map -> Bool
    empty :: map
    lookup :: k -> map -> Maybe v
    insert :: k -> v -> map -> map
    delete :: k -> map -> map
