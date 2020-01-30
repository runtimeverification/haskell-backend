module Test.Kore.Builtin.Endianness
    ( test_verify
    , test_match
    , test_unify
    ) where

import Prelude.Kore

import Test.Tasty

import qualified GHC.Stack as GHC

import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
import Kore.Step.Simplification.AndTerms
    ( termUnification
    )
import Kore.Step.Simplification.Data
    ( runSimplifier
    )
import Kore.Unification.Error
    ( UnificationOrSubstitutionError
    )
import Kore.Unification.UnifierT
    ( runUnifierT
    )
import Kore.Variables.UnifiedVariable
import SMT
    ( runNoSMT
    )

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

test_unify :: [TestTree]
test_unify =
    [ unifies "littleEndianBytes" littleEndianBytes littleEndianBytes []
    , doesn'tUnify "littleEndianBytes and bigEndianBytes"
        littleEndianBytes
        bigEndianBytes
    , unifies "bigEndianBytes" bigEndianBytes bigEndianBytes []
    , doesn'tUnify "bigEndianBytes and littleEndianBytes"
        bigEndianBytes
        littleEndianBytes
    ]
  where
    unifies
        :: GHC.HasCallStack
        => TestName
        -> TermLike Variable
        -> TermLike Variable
        -> [(UnifiedVariable Variable, TermLike Variable)]
        -> TestTree
    unifies name term1 term2 solution =
        testCase name $ do
            let expect =
                    Pattern.withCondition term1
                    $ mconcat (Condition.fromSingleSubstitution <$> solution)
            actual <- unify term1 term2
            assertEqual "expected unification solution" (Right [expect]) actual
    doesn'tUnify
        :: GHC.HasCallStack
        => TestName
        -> TermLike Variable
        -> TermLike Variable
        -> TestTree
    doesn'tUnify name term1 term2 =
        testCase name $ do
            actual <- unify term1 term2
            assertEqual "expected bottom" (Right []) actual

unify
    :: GHC.HasCallStack
    => TermLike Variable
    -> TermLike Variable
    -> IO (Either UnificationOrSubstitutionError [Pattern Variable])
unify term1 term2 =
    runNoSMT mempty
    $ runSimplifier testEnv
    $ runUnifierT
    $ termUnification term1 term2
