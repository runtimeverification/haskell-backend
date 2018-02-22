{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
module Data.Kore.Substitution.MapClass where

class Eq k => MapClass map k v | map -> k, map -> v where
    isEmpty :: map -> Bool
    lookup :: k -> map -> Maybe v
    insert :: k -> v -> map -> map
    delete :: k -> map -> map
