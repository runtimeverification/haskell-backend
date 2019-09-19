{-|
Module      : Kore.Parser.CharSet
Description : Efficient representation for a dictionary having extended ASCII
              characters as keys. Meant for internal use only.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.Parser.CharDict
    ( CharDict
    , makeCharDict
    , memoize
    , (!)
    ) where

import qualified Data.Array as Array
import Data.Maybe
    ( fromMaybe
    )

newtype CharDict a = CharDict { getCharDict :: Array.Array Char a }

memoize :: (Char -> a) -> CharDict a
memoize f =
    CharDict $ Array.array ('\0', '\255') [(c, f c) | c <- ['\0'..'\255']]

makeCharDict :: [(Char,a)] -> a -> CharDict a
makeCharDict dict defaultValue =
  CharDict $ Array.array ('\0', '\255')
      [(c, fromMaybe defaultValue (lookup c dict))| c <- ['\0'..'\255']]

(!) :: CharDict a -> Char -> a
(!) dict c = getCharDict dict Array.! c
