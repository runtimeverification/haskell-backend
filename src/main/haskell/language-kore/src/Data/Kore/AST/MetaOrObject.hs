{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE GADTs                  #-}
module Data.Kore.AST.MetaOrObject where

import           Data.Kore.AST.Common
import           Data.Typeable        (Typeable, cast)

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
    isObject l = case isMetaOrObject l of IsObject -> True; _ -> False
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
    :: forall level thing c . (MetaOrObject level)
    => thing level -> MetaOrObjectTransformer thing c -> c
applyMetaObjectFunction x trans =
  case isMetaOrObject (undefined :: level) of
    IsObject -> objectTransformer trans x
    IsMeta -> metaTransformer trans x

class Typeable thing
    => UnifiedThing unifiedThing thing | unifiedThing -> thing
  where
    destructor :: unifiedThing -> Either (thing Meta) (thing Object)
    objectConstructor :: thing Object -> unifiedThing
    metaConstructor :: thing Meta -> unifiedThing
    transformUnified
        :: (forall level . MetaOrObject level => thing level -> b)
        -> (unifiedThing -> b)
    transformUnified f unifiedStuff =
        case destructor unifiedStuff of
            Left x  -> f x
            Right x -> f x
    asUnified :: MetaOrObject level => thing level -> unifiedThing
    asUnified x = applyMetaObjectFunction x MetaOrObjectTransformer
        { objectTransformer = objectConstructor
        , metaTransformer = metaConstructor
        }
