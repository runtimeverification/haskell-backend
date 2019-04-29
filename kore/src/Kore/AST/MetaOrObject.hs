{-|
Module      : Kore.AST.MetaOrObject
Description : Specifies the 'Meta', 'Object', and 'Unified' types, and common
              functionality for them
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

-}
module Kore.AST.MetaOrObject
    ( pattern Meta
    , Meta
    , Object (..)
    ) where

type Meta = Object

pattern Meta :: Meta
pattern Meta = Object

data Object = Object
    deriving (Eq, Ord, Show)
