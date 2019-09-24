module Test.Kore.Step.Simplification.OrPattern where

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
import Kore.Internal.TermLike
    ( TermLike
    , mkElemVar
    )
import Kore.Predicate.Predicate
    ( makeAndPredicate
    , makeEqualsPredicate
    , makeTruePredicate
    )
import qualified Kore.Predicate.Predicate as Syntax
    ( Predicate
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
        actual <- runSimplifyPredicates makeTruePredicate OrPattern.top
        assertEqual "" OrPattern.top actual
    , testCase "Identity for bottom" $ do
        actual <- runSimplifyPredicates makeTruePredicate OrPattern.bottom
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
            makeTruePredicate
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
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                ]
        actual <- runSimplifyPredicates
            (positive x)
            ( OrPattern.fromPatterns
                [ Conditional
                    { term = Mock.a
                    , predicate = makeTruePredicate
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

positive :: TermLike Variable -> Syntax.Predicate Variable
positive u =
    makeEqualsPredicate
        (Mock.lessInt
            (Mock.fTestInt u)  -- wrap the given term for sort agreement
            (Mock.builtinInt 0)
        )
        (Mock.builtinBool False)

negative :: TermLike Variable -> Syntax.Predicate Variable
negative u =
    makeEqualsPredicate
        (Mock.greaterEqInt
            (Mock.fTestInt u)  -- wrap the given term for sort agreement
            (Mock.builtinInt 0)
        )
        (Mock.builtinBool False)

runSimplifyPredicates
    :: Syntax.Predicate Variable
    -> OrPattern Variable
    -> IO (OrPattern Variable)
runSimplifyPredicates predicate orPattern =
    Test.runSimplifier Mock.env
    $ simplifyPredicatesWithSmt predicate orPattern
