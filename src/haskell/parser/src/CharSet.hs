module CharSet
       ( CharSet
       , make
       , join
       , elem
       ) where

import qualified CharDict
import Prelude hiding (elem)

newtype CharSet = CharSet { getCharSet :: CharDict.CharDict Bool }

make :: String -> CharSet
make dom = CharSet $ CharDict.make (map (\x -> (x,True)) dom) False

elem :: Char -> CharSet -> Bool
c `elem` cs = getCharSet cs CharDict.! c

domain :: CharSet -> String
domain cs = filter (`elem` cs) ['\0'..'\255']

join :: CharSet -> CharSet -> CharSet
x `join` y =  make (domain x ++ domain y)
