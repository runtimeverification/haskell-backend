module Test.Kore.Builtin.Endianness
    ( test_Endianness
    ) where

import Test.Tasty

import Kore.Error
    ( assertRight
    )
import Kore.Internal.TermLike

import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import Test.Tasty.HUnit.Ext

test_Endianness :: [TestTree]
test_Endianness =
    [ testCase "verify littleEndianBytes" $ do
        let original = mkApplySymbol littleEndianBytesSymbol []
            actual = assertRight $ verifyPattern (Just endiannessSort) original
            expect = littleEndianBytes
        assertEqual "expected internal representation" expect actual
    , testCase "verify bigEndianBytes" $ do
        let original = mkApplySymbol bigEndianBytesSymbol []
            actual = assertRight $ verifyPattern (Just endiannessSort) original
            expect = bigEndianBytes
        assertEqual "expected internal representation" expect actual
    ]
