module CharDict
       ( CharDict
       , make
       , join
       , elem
       )
  where

import           Data.Array
import           Prelude hiding (elem)
import qualified Prelude (elem)

newtype CharDict = CharDict { getCharDict :: Array Char Bool }

make :: String -> CharDict
make domain =
    CharDict $
      array ('\0', '\255') [(c, c `Prelude.elem` domain)| c <- ['\0'..'\255']]

join :: CharDict -> CharDict -> CharDict
x `join` y =
    CharDict $
      array ('\0', '\255') [(c, c `elem` x || c `elem` y) | c <- ['\0'..'\255']]


elem :: Char -> CharDict -> Bool
c `elem` dict = (getCharDict dict) ! c