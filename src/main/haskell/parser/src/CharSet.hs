module CharSet
       ( CharSet
       , makeCharSet
       , join
       , elem
       ) where

import CharDict
import Prelude hiding (elem)

newtype CharSet = CharSet { getCharSet :: CharDict.CharDict Bool }

makeCharSet :: String -> CharSet
makeCharSet dom = CharSet $ makeCharDict (map (\x -> (x,True)) dom) False

elem :: Char -> CharSet -> Bool
c `elem` cs = getCharSet cs ! c

domain :: CharSet -> String
domain cs = filter (`elem` cs) ['\0'..'\255']

join :: CharSet -> CharSet -> CharSet
x `join` y =  makeCharSet (domain x ++ domain y)
