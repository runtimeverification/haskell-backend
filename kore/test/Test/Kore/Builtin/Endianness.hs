module Test.Kore.Builtin.Endianness (
    test_verify,
    test_match,
    test_unify,
) where

import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Substitution (
    Assignment,
 )
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.AndTerms (
    termUnification,
 )
import Kore.Simplify.Data (
    runSimplifier,
 )
import qualified Kore.Simplify.Not as Not
import Kore.Unification.UnifierT (
    runUnifierT,
 )
import Prelude.Kore
import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import Test.Kore.Rewrite.Axiom.Matcher (
    doesn'tMatch,
    matches,
 )
import Test.SMT (
    runNoSMT,
 )
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_verify :: [TestTree]
test_verify =
    [ test "littleEndianBytes" littleEndianBytesSymbol littleEndianBytes
    , test "bigEndianBytes" bigEndianBytesSymbol bigEndianBytes
    ]
  where
    test ::
        HasCallStack =>
        TestName ->
        Symbol ->
        TermLike VariableName ->
        TestTree
    test name symbol expect =
        testCase name $ do
            let original = mkApplySymbol symbol []
                actual = verifyPattern (Just endiannessSort) original
            assertEqual "expected verified pattern" (Right expect) actual

test_match :: [TestTree]
test_match =
    [ matches "littleEndianBytes" littleEndianBytes littleEndianBytes []
    , doesn'tMatch
        "not bigEndianBytes -> littleEndianBytes"
        littleEndianBytes
        bigEndianBytes
    , matches "bigEndianBytes" bigEndianBytes bigEndianBytes []
    , doesn'tMatch
        "not littleEndianBytes -> bigEndianBytes"
        bigEndianBytes
        littleEndianBytes
    ]

test_unify :: [TestTree]
test_unify =
    [ unifies "littleEndianBytes" littleEndianBytes littleEndianBytes []
    , doesn'tUnify
        "littleEndianBytes and bigEndianBytes"
        littleEndianBytes
        bigEndianBytes
    , unifies "bigEndianBytes" bigEndianBytes bigEndianBytes []
    , doesn'tUnify
        "bigEndianBytes and littleEndianBytes"
        bigEndianBytes
        littleEndianBytes
    ]
  where
    unifies ::
        HasCallStack =>
        TestName ->
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName ->
        [Assignment RewritingVariableName] ->
        TestTree
    unifies name term1 term2 solution =
        testCase name $ do
            let expect =
                    Pattern.withCondition term1 $
                        mconcat (Condition.fromSingleSubstitution <$> solution)
            actual <- unify term1 term2
            assertEqual "expected unification solution" [expect] actual
    doesn'tUnify ::
        HasCallStack =>
        TestName ->
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName ->
        TestTree
    doesn'tUnify name term1 term2 =
        testCase name $ do
            actual <- unify term1 term2
            assertEqual "expected bottom" [] actual

unify ::
    HasCallStack =>
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    IO [Pattern RewritingVariableName]
unify term1 term2 =
    runNoSMT $
        runSimplifier testEnv $
            runUnifierT Not.notSimplifier $
                termUnification Not.notSimplifier term1 term2
