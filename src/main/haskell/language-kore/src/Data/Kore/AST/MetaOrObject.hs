{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE GADTs                  #-}
module Data.Kore.AST.MetaOrObject where
import           Data.Proxy(Proxy(Proxy))
import           Data.Typeable        (Typeable, cast)

import           Data.Kore.AST.Common

toProxy :: a -> Proxy a
toProxy _ = Proxy

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

class Typeable thing
    => UnifiedThing unifiedThing thing | unifiedThing -> thing
  where
    destructor :: unifiedThing -> Either (thing Meta) (thing Object)
    objectConstructor :: thing Object -> unifiedThing
    metaConstructor :: thing Meta -> unifiedThing
    transformUnified
        :: (forall level . MetaOrObject level => thing level -> b)
        -> (unifiedThing -> b)
    transformUnified f unifiedStuff = either f f (destructor unifiedStuff)
    asUnified :: (MetaOrObject level) => thing level -> unifiedThing
    asUnified x = case isMetaOrObject x of
      IsMeta -> metaConstructor x
      IsObject -> objectConstructor x
