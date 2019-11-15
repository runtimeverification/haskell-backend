module Test.Kore.Builtin.Endianness
    ( test_verify
    , test_match
    ) where

import Test.Tasty

import qualified GHC.Stack as GHC

import Kore.Internal.TermLike

import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import Test.Kore.Step.Axiom.Matcher
    ( doesn'tMatch
    , matches
    )
import Test.Tasty.HUnit.Ext

test_verify :: [TestTree]
test_verify =
    [ test "littleEndianBytes" littleEndianBytesSymbol littleEndianBytes
    , test "bigEndianBytes" bigEndianBytesSymbol bigEndianBytes
    ]
  where
    test
        :: GHC.HasCallStack
        => TestName
        -> Symbol
        -> TermLike Variable
        -> TestTree
    test name symbol expect =
        testCase name $ do
            let original = mkApplySymbol symbol []
                actual = verifyPattern (Just endiannessSort) original
            assertEqual "expected verified pattern" (Right expect) actual

test_match :: [TestTree]
test_match =
    [ matches "littleEndianBytes" littleEndianBytes littleEndianBytes []
    , doesn'tMatch "not bigEndianBytes -> littleEndianBytes"
        littleEndianBytes
        bigEndianBytes
    , matches "bigEndianBytes" bigEndianBytes bigEndianBytes []
    , doesn'tMatch "not littleEndianBytes -> bigEndianBytes"
        bigEndianBytes
        littleEndianBytes
    ]
