{-# LANGUAGE NoImplicitPrelude #-}

module Data.Map.Dynamic
    ( DynamicMap
    -- * Construction
    , empty
    , singleton
    -- * Basic interface
    , null
    , size
    , member
    , lookup
    , insert
    , delete
    ) where

import           Data.Dynamic
import           Data.Function
import           Data.Hashable
import           Data.HashMap.Strict
                 ( HashMap )
import qualified Data.HashMap.Strict as HashMap
import           Data.Maybe
import           Data.Proxy
import           Prelude hiding
                 ( lookup, null )
import           Type.Reflection

{- | Dynamic keys.
 -}
data Key where
    Key
        ::  forall key value
        .   (Eq key, Hashable key)
        => !(TypeRep key)
        -> !(TypeRep value)
        -> !key
        -> Key

instance Eq Key where
    (==) (Key repKey1 repValue1 key1) (Key repKey2 repValue2 key2) =
        do
            HRefl <- eqTypeRep repKey1   repKey2
            HRefl <- eqTypeRep repValue1 repValue2
            return (key1 == key2)
        & fromMaybe False

instance Hashable Key where
    hashWithSalt salt (Key repKey repValue key) =
        salt `hashWithSalt` repKey `hashWithSalt` repValue `hashWithSalt` key

newtype DynamicMap = DynamicMap { getDynamicMap :: HashMap Key Dynamic }

empty :: DynamicMap
empty = DynamicMap HashMap.empty

singleton
    :: forall key value
    .  (Eq key, Hashable key, Typeable key, Typeable value)
    => key -> value -> DynamicMap
singleton key value =
    DynamicMap (HashMap.singleton (Key repKey repValue key) (toDyn value))
  where
    repKey = typeRep @key
    repValue = typeRep @value

null :: DynamicMap -> Bool
null = HashMap.null . getDynamicMap

size :: DynamicMap -> Int
size = HashMap.size . getDynamicMap

member
    :: forall key value
    .  (Eq key, Hashable key, Typeable key, Typeable value)
    => key -> Proxy value -> DynamicMap -> Bool
member key Proxy =
    HashMap.member (Key repKey repValue key) . getDynamicMap
  where
    repKey = typeRep @key
    repValue = typeRep @value

lookup
    :: forall key value
    .  (Eq key, Hashable key, Typeable key, Typeable value)
    => key -> DynamicMap -> Maybe value
lookup key dynamicMap = do
    unwrapValue <$> HashMap.lookup key' (getDynamicMap dynamicMap)
  where
    key' = Key (typeRep @key) (typeRep @value) key
    -- Unwrap a Dynamic value; throws an error if the wrapped value
    -- has the wrong type. The type is assured by 'insert'.
    unwrapValue = fromJust . fromDynamic

insert
    :: forall key value
    .  (Eq key, Hashable key, Typeable key, Typeable value)
    => key -> value -> DynamicMap -> DynamicMap
insert key value =
    DynamicMap . HashMap.insert key' (toDyn value) . getDynamicMap
  where
    key' = Key (typeRep @key) (typeRep @value) key

delete
    :: forall key value
    .  (Eq key, Hashable key, Typeable key, Typeable value)
    => key -> Proxy value -> DynamicMap -> DynamicMap
delete key Proxy =
    DynamicMap . HashMap.delete key' . getDynamicMap
  where
    key' = Key (typeRep @key) (typeRep @value) key
