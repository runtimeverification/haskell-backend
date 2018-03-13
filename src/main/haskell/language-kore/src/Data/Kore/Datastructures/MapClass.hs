{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
module Data.Kore.Datastructures.MapClass ( EmptyTestable(..)
                                         , MapClass(..)
                                         ) where

import           Data.Kore.Datastructures.EmptyTestable

class (Eq k, EmptyTestable map) => MapClass map k v | map -> k, map -> v where
    lookup :: k -> map -> Maybe v
    insert :: k -> v -> map -> map
    delete :: k -> map -> map
