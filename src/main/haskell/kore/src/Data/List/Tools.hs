{-|
Module      : Data.List.Tools
Description : Data structures and functions missing from the actual Data.List.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}

module Data.List.Tools where

{-| 'crossProduct' computes the cross-product of two lists.
-}
crossProduct
    :: [child1]
    -> [child2]
    -> [(child1, child2)]
crossProduct first second =
    [(x, y) | x <- first, y <- second]
