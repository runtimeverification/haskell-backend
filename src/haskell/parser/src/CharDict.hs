module CharDict
       ( CharDict
       , make
       , memoize
       , (!)
       )
  where

import qualified Data.Array as Array
import           Data.Maybe (fromMaybe)

newtype CharDict a = CharDict { getCharDict :: Array.Array Char a }

memoize :: (Char -> a) -> CharDict a
memoize f =
    CharDict $ Array.array ('\0', '\255') [(c, f c) | c <- ['\0'..'\255']]

make :: [(Char,a)] -> a -> CharDict a
make dict defaultValue =
  CharDict $ Array.array ('\0', '\255')
      [(c, fromMaybe defaultValue (lookup c dict))| c <- ['\0'..'\255']]

(!) :: CharDict a -> Char -> a
dict ! c = (getCharDict dict) Array.! c
