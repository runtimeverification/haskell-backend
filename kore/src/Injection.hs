module Injection
    ( Injection (..)
    , Prism'
    ) where

import Prelude

import Control.Lens
    ( Prism'
    )
import qualified Control.Lens as Lens
import Data.Dynamic
    ( Dynamic
    , Typeable
    , fromDynamic
    , toDyn
    )

{- | The canonical injection or inclusion of @from ↪ into@.

We can think of @into@ being a sum type with @from@ the type of one of its
constructors, although it need not be implemented this way.

It is illustrative to consider the instance for 'Maybe':

@
instance Injection (Maybe a) a where
    inject  = Just
    retract = id
@

Left identity:

@
retract (inject x) = Just x
@

Note: left identity implies that @inject@ is indeed injective.

Invertibility, over the range of @retract@:

@
retract x = Just a => x = inject a
@

Note: invertibility is actually implied by the left identity property, provided
@inject@ and @retract@ are total functions.

 -}
class Injection into from where
    {-# MINIMAL injection | ( inject, retract ) #-}

    injection :: Prism' into from
    injection = Lens.prism' inject retract
    {-# INLINE injection #-}

    inject :: from -> into
    inject = Lens.review injection
    {-# INLINE inject #-}

    retract :: into -> Maybe from
    retract = Lens.preview injection
    {-# INLINE retract #-}

instance Injection (Maybe a) a where
    inject = Just
    {-# INLINE inject #-}

    retract = id
    {-# INLINE retract #-}

instance Typeable a => Injection Dynamic a where
    inject = toDyn
    {-# INLINE inject #-}

    retract = fromDynamic
    {-# INLINE retract #-}
