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
    , MetaOrObject (..)
    , toProxy
    , ShowMetaOrObject
    , EqMetaOrObject
    , OrdMetaOrObject
    , IsMetaOrObject (..)
    ) where

import Data.Proxy
       ( Proxy (Proxy) )

toProxy :: a -> Proxy a
toProxy _ = Proxy

type Meta = Object

pattern Meta :: Meta
pattern Meta = Object

data Object = Object
    deriving (Eq, Ord, Show)

data IsMetaOrObject s where
    IsObject :: IsMetaOrObject Object

instance Show (IsMetaOrObject s) where
    show IsObject = "Object"


{-|Class identifying a Kore level. It should only be implemented by the
'Object' and 'Meta' types, and should verify:

* @ isObject Object && not (isMeta Object) @
* @ not (isObject Meta) && isMeta Meta @
-}
class (level ~ Object) => MetaOrObject level where
    isMetaOrObject :: proxy level -> IsMetaOrObject level
    isMetaOrObject _ = IsObject

    isObject :: level -> Bool
    isObject _ = True

    isMeta :: level -> Bool
    isMeta _ = False

instance (level ~ Object) => MetaOrObject level

type ShowMetaOrObject thing = (Show (thing Meta), Show (thing Object))
type EqMetaOrObject thing = (Eq (thing Meta), Eq (thing Object))
type OrdMetaOrObject thing = (Ord (thing Meta), Ord (thing Object))
