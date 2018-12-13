module Test.Kore.Step.OrOfExpandedPattern where

import           Hedgehog
                 ( Property, (===) )
import qualified Hedgehog

import Kore.AST.MetaOrObject
import Kore.Step.OrOfExpandedPattern

import Test.Kore

-- | Check that 'merge' preserves the @\\or@-idempotency condition.
hprop_mergeIdemOr :: Property
hprop_mergeIdemOr = Hedgehog.property $ do
    ors <- Hedgehog.forAll (standaloneGen $ orOfExpandedPatternGen @Object)
    merge ors ors === ors

hprop_makeIdemOr :: Property
hprop_makeIdemOr = Hedgehog.property $ do
    pat <- Hedgehog.forAll (standaloneGen $ expandedPatternGen @Object)
    make [pat, pat] === make [pat]

hprop_flattenIdemOr :: Property
hprop_flattenIdemOr = Hedgehog.property $ do
    ors <- Hedgehog.forAll (standaloneGen $ orOfExpandedPatternGen @Object)
    let nested = MultiOr [ors, ors]
    flatten nested === ors
