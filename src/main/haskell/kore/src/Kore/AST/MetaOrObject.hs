{-|
Module      : Kore.AST.MetaOrObject
Description : Specifies the 'Meta', 'Object', and 'Unified' types, and common
              functionality for them
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

-}
module Kore.AST.MetaOrObject
    ( Meta (..)
    , Object (..)
    , MetaOrObject (..)
    , Unified (..)
    , asUnified
    , applyUnified
    , transformUnified
    , mapUnified
    , sequenceUnified
    , toProxy
    , ShowMetaOrObject
    , EqMetaOrObject
    , OrdMetaOrObject
    , IsMetaOrObject (..)
    ) where

import Control.DeepSeq
       ( NFData )
import Data.Proxy
       ( Proxy (Proxy) )
import GHC.Generics
       ( Generic )

import Kore.AST.Pretty
       ( Pretty (..) )

toProxy :: a -> Proxy a
toProxy _ = Proxy

data Meta = Meta
    deriving (Eq, Ord, Show)

data Object = Object
    deriving (Eq, Ord, Show)

data IsMetaOrObject s where
    IsMeta :: IsMetaOrObject Meta
    IsObject :: IsMetaOrObject Object

instance Show (IsMetaOrObject s) where
    show IsMeta   = "Meta"
    show IsObject = "Object"


{-|Class identifying a Kore level. It should only be implemented by the
'Object' and 'Meta' types, and should verify:

* @ isObject Object && not (isMeta Object) @
* @ not (isObject Meta) && isMeta Meta @
-}
class (Show level, Ord level, Eq level)
    => MetaOrObject level
  where
    isMetaOrObject :: proxy level -> IsMetaOrObject level
    isObject :: level -> Bool
    isObject l = case isMetaOrObject (toProxy l) of IsObject -> True; _ -> False
    isMeta :: level -> Bool
    isMeta l = case isMetaOrObject (toProxy l) of IsMeta -> True; _ -> False
    {-# MINIMAL isMetaOrObject #-}

instance MetaOrObject Meta where
    isMetaOrObject _ = IsMeta
instance MetaOrObject Object where
    isMetaOrObject _ = IsObject

{-|'Unified' provides a means to group together objects which are either
'Meta' or 'Object'.
-}
data Unified thing
    = UnifiedObject !(thing Object)
    | UnifiedMeta !(thing Meta)
  deriving (Generic)

type ShowMetaOrObject thing = (Show (thing Meta), Show (thing Object))
type EqMetaOrObject thing = (Eq (thing Meta), Eq (thing Object))
type OrdMetaOrObject thing = (Ord (thing Meta), Ord (thing Object))

deriving instance (EqMetaOrObject thing) => Eq (Unified thing)
deriving instance (OrdMetaOrObject thing) => Ord (Unified thing)
deriving instance (ShowMetaOrObject thing) => Show (Unified thing)

instance (NFData (thing Meta), NFData (thing Object)) => NFData (Unified thing)

instance
    ( Pretty (thing Object)
    , Pretty (thing Meta)
    ) => Pretty (Unified thing)
  where
    pretty = applyUnified pretty pretty

{-|Given a function transforming objects of 'Meta' type and another transforming
objects of 'Object' type, 'applyUnified' builds the corresponding direct sum
function combining their effects to transform an 'Unified' object.
-}
applyUnified
    :: (thing Meta -> b)
    -> (thing Object -> b)
    -> (Unified thing -> b)
applyUnified metaT _ (UnifiedMeta x)     = metaT x
applyUnified _ objectT (UnifiedObject x) = objectT x

{-|Given a function transforming objects of any 'level', 'transformUnified'
"lifts" the function to apply on 'Unified' objects.
-}
transformUnified
    :: (forall level . MetaOrObject level => thing level -> b)
    -> (Unified thing -> b)
transformUnified f = applyUnified f f

{-|Given a function transforming @thing1 level@ objects into @thing2 level@ ones,
it builds one transforming 'Unified' @thing1@ objects into 'Unified' @thing2@
ones.

Its functionality is akin fo that of 'Functor.fmap'
-}
mapUnified
    :: (forall level . MetaOrObject level => thing1 level -> thing2 level)
    -> (Unified thing1 -> Unified thing2)
mapUnified f (UnifiedObject o) = UnifiedObject (f o)
mapUnified f (UnifiedMeta o)   = UnifiedMeta (f o)

{-|Given a function transforming @thing1 level@ objects into an action
producing @thing2 level@ objects,
it builds one transforming 'Unified' @thing1@ objects into
actions procuding 'Unified' @thing2@ objects.

Its functionality is akin fo that of 'Applicative.sequence'
-}
sequenceUnified
    :: Applicative a
    => (forall level . MetaOrObject level => thing1 level -> a (thing2 level))
    -> (Unified thing1 -> a (Unified thing2))
sequenceUnified f (UnifiedObject o) = UnifiedObject <$> f o
sequenceUnified f (UnifiedMeta o)   = UnifiedMeta <$> f o

{-|'asUnified' takes an arbitrary 'Meta' or 'Object' @thing@ and transforms it
into the corresponding 'Unified' @thing@.
-}
asUnified
    :: MetaOrObject level => thing level -> Unified thing
asUnified x = case isMetaOrObject x of
    IsObject -> UnifiedObject x
    IsMeta   -> UnifiedMeta x
