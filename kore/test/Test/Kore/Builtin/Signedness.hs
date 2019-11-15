module Test.Kore.Builtin.Signedness
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
    [ test "littleSignedBytes" signedBytesSymbol signedBytes
    , test "verify bigSignedBytes" unsignedBytesSymbol unsignedBytes
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
                actual = verifyPattern (Just signednessSort) original
            assertEqual "expected verified pattern" (Right expect) actual

test_match :: [TestTree]
test_match =
    [ matches "signedBytes" signedBytes signedBytes []
    , doesn'tMatch "not unsignedBytes -> signedBytes"
        signedBytes
        unsignedBytes
    , matches "unsignedBytes" unsignedBytes unsignedBytes []
    , doesn'tMatch "not signedBytes -> unsignedBytes"
        unsignedBytes
        signedBytes
    ]
