module Test.Kore.Builtin.Signedness
    ( test_Signedness
    ) where

import Test.Tasty

import Kore.Error
    ( assertRight
    )
import Kore.Internal.TermLike

import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import Test.Tasty.HUnit.Ext

test_Signedness :: [TestTree]
test_Signedness =
    [ testCase "verify littleSignedBytes" $ do
        let original = mkApplySymbol signedBytesSymbol []
            actual = assertRight $ verifyPattern (Just signednessSort) original
            expect = signedBytes
        assertEqual "expected internal representation" expect actual
    , testCase "verify bigSignedBytes" $ do
        let original = mkApplySymbol unsignedBytesSymbol []
            actual = assertRight $ verifyPattern (Just signednessSort) original
            expect = unsignedBytes
        assertEqual "expected internal representation" expect actual
    ]
