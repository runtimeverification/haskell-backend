module Test.Kore.Step.Simplification.OrPattern
    ( test_orPatternSimplification
    ) where

import Test.Tasty

import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import qualified Kore.Internal.Conditional as Conditional.DoNotUse
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
    ( fromPatterns
    )
import qualified Kore.Internal.OrPattern as OrPattern
    ( bottom
    , top
    )
import Kore.Internal.Predicate
    ( makeAndPredicate
    , makeEqualsPredicate_
    , makeTruePredicate_
    )
import Kore.Internal.Predicate
    ( Predicate
    )
import Kore.Internal.TermLike
    ( TermLike
    , mkElemVar
    )
import Kore.Step.Simplification.OrPattern
import Kore.Syntax.Variable
    ( Variable
    )

import qualified Test.Kore.Step.MockSymbols as Mock
import qualified Test.Kore.Step.Simplification as Test
import Test.Tasty.HUnit.Ext

test_orPatternSimplification :: [TestTree]
test_orPatternSimplification =
    [ testCase "Identity for top" $ do
        actual <- runSimplifyPredicates makeTruePredicate_ OrPattern.top
        assertEqual "" OrPattern.top actual
    , testCase "Identity for bottom" $ do
        actual <- runSimplifyPredicates makeTruePredicate_ OrPattern.bottom
        assertEqual "" OrPattern.bottom actual
    , testCase "Filters with SMT" $ do
        let expected = OrPattern.fromPatterns
                [ Conditional
                    { term = Mock.a
                    , predicate = positive x
                    , substitution = mempty
                    }
                ]
        actual <- runSimplifyPredicates
            makeTruePredicate_
            ( OrPattern.fromPatterns
                [ Conditional
                    { term = Mock.a
                    , predicate = positive x
                    , substitution = mempty
                    }
                , Conditional
                    { term = Mock.b
                    , predicate = makeAndPredicate (positive x) (negative x)
                    , substitution = mempty
                    }
                ]
            )
        assertEqual "" expected actual
    , testCase "Filters with SMT and additional predicate" $ do
        let expected = OrPattern.fromPatterns
                [ Conditional
                    { term = Mock.a
                    , predicate = makeTruePredicate_
                    , substitution = mempty
                    }
                ]
        actual <- runSimplifyPredicates
            (positive x)
            ( OrPattern.fromPatterns
                [ Conditional
                    { term = Mock.a
                    , predicate = makeTruePredicate_
                    , substitution = mempty
                    }
                , Conditional
                    { term = Mock.b
                    , predicate = negative x
                    , substitution = mempty
                    }
                ]
            )
        assertEqual "" expected actual
    ]
  where
    x :: TermLike Variable
    x = mkElemVar Mock.x

positive :: TermLike Variable -> Predicate Variable
positive u =
    makeEqualsPredicate_
        (Mock.lessInt
            (Mock.fTestInt u)  -- wrap the given term for sort agreement
            (Mock.builtinInt 0)
        )
        (Mock.builtinBool False)

negative :: TermLike Variable -> Predicate Variable
negative u =
    makeEqualsPredicate_
        (Mock.greaterEqInt
            (Mock.fTestInt u)  -- wrap the given term for sort agreement
            (Mock.builtinInt 0)
        )
        (Mock.builtinBool False)

runSimplifyPredicates
    :: Predicate Variable
    -> OrPattern Variable
    -> IO (OrPattern Variable)
runSimplifyPredicates predicate orPattern =
    Test.runSimplifier Mock.env
    $ simplifyConditionsWithSmt predicate orPattern
