{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Kore.AST.MetaOrObject where

data Meta = Meta
    deriving (Show, Eq, Ord)

data Object = Object
    deriving (Show, Eq, Ord)

data IsMetaOrObject s where
    IsMeta :: IsMetaOrObject Meta
    IsObject :: IsMetaOrObject Object

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

data MetaOrObjectTransformer thing result = MetaOrObjectTransformer
    { metaTransformer   :: thing Meta -> result
    , objectTransformer :: thing Object -> result
    }

applyMetaObjectFunction
    :: forall level thing c . MetaOrObject level
    => MetaOrObjectTransformer thing c -> thing level -> c
applyMetaObjectFunction trans x =
    case isMetaOrObject (undefined :: level) of
        IsObject -> objectTransformer trans x
        IsMeta   -> metaTransformer trans x

data Unified thing
    = UnifiedObject !(thing Object)
    | UnifiedMeta !(thing Meta)

deriving instance (Eq (sort Object), Eq (sort Meta)) => Eq (Unified sort)
deriving instance (Ord (sort Object), Ord (sort Meta)) => Ord (Unified sort)
deriving instance (Show (sort Object), Show (sort Meta)) => Show (Unified sort)

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
transformUnified f (UnifiedObject o) = f o
transformUnified f (UnifiedMeta o)   = f o

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
asUnified = applyMetaObjectFunction MetaOrObjectTransformer
    { objectTransformer = UnifiedObject
    , metaTransformer = UnifiedMeta
    }


class (Show (thing Meta), Show (thing Object)) => ShowMetaOrObject thing

class (Eq (thing Meta), Eq (thing Object)) => EqMetaOrObject thing

class (Ord (thing Meta), Ord (thing Object)) => OrdMetaOrObject thing
