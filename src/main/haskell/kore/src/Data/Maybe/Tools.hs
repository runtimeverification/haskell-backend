{-|
Module      : Data.Maybe.Tools
Description : Data structures and functions missing from the actual Data.Maybe.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}

module Data.Maybe.Tools where

import Data.Maybe
       ( catMaybes, listToMaybe )

{-| Retuns the first Just value in the given list. If the list does not
contain a Just, returns Nothing.
-}
firstMaybe :: [Maybe a] -> Maybe a
firstMaybe = listToMaybe . catMaybes
