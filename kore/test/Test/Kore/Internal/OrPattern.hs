module Test.Kore.Internal.OrPattern where

import Hedgehog
    ( Property
    , (===)
    )
import qualified Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Syntax.Variable

import Test.Kore
import Test.Kore.Internal.Pattern
    ( internalPatternGen
    )

orPatternGen :: Gen (OrPattern Variable)
orPatternGen =
    OrPattern.fromPatterns <$> Gen.list (Range.linear 0 64) internalPatternGen

-- | Check that 'merge' preserves the @\\or@-idempotency condition.
hprop_mergeIdemOr :: Property
hprop_mergeIdemOr = Hedgehog.property $ do
    ors <- Hedgehog.forAll (standaloneGen orPatternGen)
    MultiOr.merge ors ors === ors

hprop_makeIdemOr :: Property
hprop_makeIdemOr = Hedgehog.property $ do
    pat <- Hedgehog.forAll (standaloneGen internalPatternGen)
    OrPattern.fromPatterns [pat, pat] === OrPattern.fromPatterns [pat]

hprop_flattenIdemOr :: Property
hprop_flattenIdemOr = Hedgehog.property $ do
    ors <- Hedgehog.forAll (standaloneGen orPatternGen)
    let nested = MultiOr.make [ors, ors]
    MultiOr.flatten nested === ors
