module Test.Kore.Step.OrPattern where

import           Hedgehog
                 ( Property, (===) )
import qualified Hedgehog

import qualified Kore.Step.OrPattern as OrPattern
import qualified Kore.Step.Representation.MultiOr as MultiOr

import Test.Kore

-- | Check that 'merge' preserves the @\\or@-idempotency condition.
hprop_mergeIdemOr :: Property
hprop_mergeIdemOr = Hedgehog.property $ do
    ors <- Hedgehog.forAll (standaloneGen $ orPatternGen)
    MultiOr.merge ors ors === ors

hprop_makeIdemOr :: Property
hprop_makeIdemOr = Hedgehog.property $ do
    pat <- Hedgehog.forAll (standaloneGen expandedPatternGen)
    OrPattern.fromPatterns [pat, pat] === OrPattern.fromPatterns [pat]

hprop_flattenIdemOr :: Property
hprop_flattenIdemOr = Hedgehog.property $ do
    ors <- Hedgehog.forAll (standaloneGen $ orPatternGen)
    let nested = MultiOr.make [ors, ors]
    MultiOr.flatten nested === ors
