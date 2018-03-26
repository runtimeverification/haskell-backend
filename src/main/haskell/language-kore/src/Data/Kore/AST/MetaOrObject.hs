{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE Rank2Types             #-}
module Data.Kore.AST.MetaOrObject where

import           Data.Kore.AST.Common
import           Data.Typeable        (Typeable, cast)

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
