module Test.Kore.Builtin.IO (
   test_logString,
 ) where

import Hedgehog
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.TermLike
import Prelude.Kore
import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import Test.Kore.Builtin.String (
    genString,
    asInternal,
 )
import Test.SMT
import Test.Tasty

test_logString :: TestTree
test_logString =
    testPropertyWithSolver "test IO.logString" $ do
        a <- forAll genString
        let expect = OrPattern.fromTermLike $ mkApplySymbol dotkSymbol []
        actual <- evaluateTermT $ mkApplySymbol logStringSymbol (asInternal <$> [a])
        (===) expect actual
