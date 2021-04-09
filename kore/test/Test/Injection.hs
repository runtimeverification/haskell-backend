{-# LANGUAGE AllowAmbiguousTypes #-}

module Test.Injection (
    hpropInjection,
    hprop_Injection_Maybe,
    hprop_Injection_Dynamic,

    -- * Re-exports
    module Hedgehog,
    Int8,
    genInt8,
) where

import Data.Dynamic (
    Dynamic,
 )
import Data.Int (
    Int8,
 )
import Hedgehog hiding (
    test,
 )
import qualified Hedgehog.Gen as Gen
import Injection
import Prelude

{- | Create a property test for an 'Injection' instance.

Only the "left identity" property is tested; as long as the instance is not
partial, this property implies all others.

Note: The @into@ type parameter *must* be specified by type application.
-}
hpropInjection ::
    forall into from.
    (Eq from, Show from) =>
    Injection into from =>
    Gen from ->
    Property
hpropInjection genFrom =
    property $ do
        from <- forAll genFrom
        let into = inject @into from
        retract into === Just from

genInt8 :: MonadGen m => m Int8
genInt8 = Gen.enumBounded

hprop_Injection_Maybe :: Property
hprop_Injection_Maybe = hpropInjection @(Maybe Int8) genInt8

hprop_Injection_Dynamic :: Property
hprop_Injection_Dynamic = hpropInjection @Dynamic genInt8
