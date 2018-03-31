{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE UndecidableInstances   #-}
module Data.Kore.AST.MetaOrObject where

import           Data.Typeable (Typeable, cast)

data Meta = Meta
    deriving (Show, Eq, Ord, Typeable)

data Object = Object
    deriving (Show, Eq, Ord, Typeable)

{-|Class identifying a Kore level. It should only be implemented by the
'Object' and 'Meta' types, and should verify:

* @ isObject Object && not (isMeta Object) @
* @ not (isObject Meta) && isMeta Meta @
-}
class (Show level, Ord level, Eq level, Typeable level)
    => MetaOrObject level
  where
    isObject :: level -> Bool
    isMeta :: level -> Bool
    isObject = not . isMeta
    isMeta = not . isObject
    {-# MINIMAL isObject | isMeta #-}

instance MetaOrObject Meta where
    isMeta _ = True
instance MetaOrObject Object where
    isObject _ = True

data MetaOrObjectTransformer thing result = MetaOrObjectTransformer
    { metaTransformer   :: thing Meta -> result
    , objectTransformer :: thing Object -> result
    }

applyMetaObjectFunction
    :: (Typeable thing, MetaOrObject level)
    => thing level -> MetaOrObjectTransformer thing c -> c
applyMetaObjectFunction x = applyMetaObjectFunctionCasted (cast x) (cast x)
applyMetaObjectFunctionCasted
    :: Maybe (thing Object)
    -> Maybe (thing Meta)
    -> MetaOrObjectTransformer thing c
    -> c
applyMetaObjectFunctionCasted (Just x) Nothing f = objectTransformer f x
applyMetaObjectFunctionCasted Nothing (Just x) f = metaTransformer f x
applyMetaObjectFunctionCasted _ _ _ =
    error "applyMetaObjectFunctionCasted: this should not happen!"

data Unified thing
    = UnifiedObject !(thing Object)
    | UnifiedMeta !(thing Meta)

deriving instance (Eq (sort Object), Eq (sort Meta)) => Eq (Unified sort)
deriving instance (Ord (sort Object), Ord (sort Meta)) => Ord (Unified sort)
deriving instance (Show (sort Object), Show (sort Meta)) => Show (Unified sort)
deriving instance
    ( Typeable (sort Object)
    , Typeable (sort Meta)
    ) => Typeable (Unified sort)

applyUnified
    :: (forall level . MetaOrObject level => thing level -> b)
    -> (Unified thing -> b)
applyUnified f (UnifiedObject o) = f o
applyUnified f (UnifiedMeta o)   = f o

mapUnified
    :: (forall level . MetaOrObject level => thing1 level -> thing2 level)
    -> (Unified thing1 -> Unified thing2)
mapUnified f (UnifiedObject o) = UnifiedObject (f o)
mapUnified f (UnifiedMeta o)   = UnifiedMeta (f o)

sequenceUnified
    :: Applicative a
    => (forall level . MetaOrObject level => thing1 level -> a (thing2 level))
    -> (Unified thing1 -> a (Unified thing2))
sequenceUnified f (UnifiedObject o) = UnifiedObject <$> f o
sequenceUnified f (UnifiedMeta o)   = UnifiedMeta <$> f o

asUnified
    :: (MetaOrObject level, Typeable thing) => thing level -> Unified thing
asUnified x = applyMetaObjectFunction x MetaOrObjectTransformer
    { objectTransformer = UnifiedObject
    , metaTransformer = UnifiedMeta
    }


class (Show (thing Meta), Show (thing Object)) => ShowMetaOrObject thing

class (Eq (thing Meta), Eq (thing Object)) => EqMetaOrObject thing

class (Ord (thing Meta), Ord (thing Object)) => OrdMetaOrObject thing
