{-|
Module      : Data.Map.Class
Description : Class for representing a @key@ |-> @value@ map functionality.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Data.Map.Class where

-- | 'MapClass' describes a @map@ from @key@s to @value@s
class Eq key => MapClass map key value where
    -- |'isEmpty' tells whether the map is empty
    isEmpty :: map key value -> Bool
    empty :: map key value
    lookup :: key -> map key value -> Maybe value
    insert :: key -> value -> map key value -> map key value
    delete :: key -> map key value -> map key value
