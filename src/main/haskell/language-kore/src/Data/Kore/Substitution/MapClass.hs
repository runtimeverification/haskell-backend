{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
module Data.Kore.Substitution.MapClass where

-- |Converting back and forth from maps to list of key-value pairs
class MapClass map k v | map -> k, map -> v where
    fromList :: Eq k => [(k,v)] -> map
    toList :: map -> [(k,v)]
    isEmpty :: map -> Bool
    lookup :: Eq k => k -> map -> Maybe v
