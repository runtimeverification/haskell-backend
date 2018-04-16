{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Kore.AST.MetaOrObject
    ( Meta (..)
    , Object (..)
    , MetaOrObject (isObject, isMeta)
    , Unified (..)
    , asUnified
    , transformUnified
    , mapUnified
    , sequenceUnified
    , ShowMetaOrObject
    , EqMetaOrObject
    , OrdMetaOrObject
    , getMetaOrObjectType
    , IsMetaOrObject (..)
    ) where

data Meta = Meta
    deriving (Show, Eq, Ord)

data Object = Object
    deriving (Show, Eq, Ord)

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
    isMetaOrObject :: level -> IsMetaOrObject level
    isObject :: level -> Bool
    isObject l =  case isMetaOrObject l of IsObject -> True; _ -> False
    isMeta :: level -> Bool
    isMeta l = case isMetaOrObject l of IsMeta -> True; _ -> False
    {-# MINIMAL isMetaOrObject #-}

instance MetaOrObject Meta where
    isMetaOrObject _ = IsMeta
instance MetaOrObject Object where
    isMetaOrObject _ = IsObject

getMetaOrObjectType :: MetaOrObject level => thing level -> IsMetaOrObject level
getMetaOrObjectType _ = isMetaOrObject (undefined :: level)

data Unified thing
    = UnifiedObject !(thing Object)
    | UnifiedMeta !(thing Meta)

type ShowMetaOrObject thing = (Show (thing Meta), Show (thing Object))
type EqMetaOrObject thing = (Eq (thing Meta), Eq (thing Object))
type OrdMetaOrObject thing = (Ord (thing Meta), Ord (thing Object))

deriving instance (EqMetaOrObject thing) => Eq (Unified thing)
deriving instance (OrdMetaOrObject thing) => Ord (Unified thing)
deriving instance (ShowMetaOrObject thing) => Show (Unified thing)

applyUnified
    :: (thing Meta -> b)
    -> (thing Object -> b)
    -> (Unified thing -> b)
applyUnified metaT objectT =
    \case
        UnifiedMeta x -> metaT x
        UnifiedObject x -> objectT x

transformUnified
    :: (forall level . MetaOrObject level => thing level -> b)
    -> (Unified thing -> b)
transformUnified f = applyUnified f f

mapUnified
    :: (forall level . thing1 level -> thing2 level)
    -> (Unified thing1 -> Unified thing2)
mapUnified f (UnifiedObject o) = UnifiedObject (f o)
mapUnified f (UnifiedMeta o)   = UnifiedMeta (f o)

sequenceUnified
    :: Applicative a
    => (forall level . thing1 level -> a (thing2 level))
    -> (Unified thing1 -> a (Unified thing2))
sequenceUnified f (UnifiedObject o) = UnifiedObject <$> f o
sequenceUnified f (UnifiedMeta o)   = UnifiedMeta <$> f o

asUnified
    :: MetaOrObject level => thing level -> Unified thing
asUnified x = case getMetaOrObjectType x of
    IsObject -> UnifiedObject x
    IsMeta   -> UnifiedMeta x
