module Test.Kore.Step.Representation.OrOfExpandedPattern where

import           Hedgehog
                 ( Property, (===) )
import qualified Hedgehog

import           Kore.AST.MetaOrObject
import qualified Kore.Step.Representation.MultiOr as MultiOr

import Test.Kore

-- | Check that 'merge' preserves the @\\or@-idempotency condition.
hprop_mergeIdemOr :: Property
hprop_mergeIdemOr = Hedgehog.property $ do
    ors <- Hedgehog.forAll (standaloneGen $ orOfExpandedPatternGen @Object)
    MultiOr.merge ors ors === ors

hprop_makeIdemOr :: Property
hprop_makeIdemOr = Hedgehog.property $ do
    pat <- Hedgehog.forAll (standaloneGen $ expandedPatternGen @Object)
    MultiOr.make [pat, pat] === MultiOr.make [pat]

hprop_flattenIdemOr :: Property
hprop_flattenIdemOr = Hedgehog.property $ do
    ors <- Hedgehog.forAll (standaloneGen $ orOfExpandedPatternGen @Object)
    let nested = MultiOr.make [ors, ors]
    MultiOr.flatten nested === ors
