{-|
Module      : Kore.Parser.CharSet
Description : Efficient representation for a set of extended ASCII characters.
              Meant for internal use only.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.Parser.CharSet
    ( CharSet
    , makeCharSet
    , join
    , elem
    ) where

import Prelude hiding
    ( elem
    )

import Kore.Parser.CharDict as CharDict

newtype CharSet = CharSet { getCharSet :: CharDict.CharDict Bool }

makeCharSet :: String -> CharSet
makeCharSet dom = CharSet $ makeCharDict (map (\x -> (x,True)) dom) False

elem :: Char -> CharSet -> Bool
c `elem` cs = getCharSet cs ! c

domain :: CharSet -> String
domain cs = filter (`elem` cs) ['\0'..'\255']

join :: CharSet -> CharSet -> CharSet
x `join` y =  makeCharSet (domain x ++ domain y)
