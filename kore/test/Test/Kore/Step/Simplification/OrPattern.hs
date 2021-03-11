{-# LANGUAGE Strict #-}

module Test.Kore.Step.Simplification.OrPattern
    ( test_orPatternSimplification
    ) where

import Prelude.Kore

import Test.Tasty

import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import qualified Kore.Internal.Conditional as Conditional.DoNotUse
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
    ( bottom
    , fromPatterns
    , top
    )
import Kore.Internal.Predicate
    ( Predicate
    , makeAndPredicate
    , makeEqualsPredicate
    , makeEqualsPredicate
    , makeTruePredicate
    , makeTruePredicate
    )
import qualified Kore.Internal.SideCondition as SideCondition
    ( assumeTruePredicate
    )
import Kore.Internal.TermLike
    ( TermLike
    , mkElemVar
    )
import Kore.Rewriting.RewritingVariable
    ( RewritingVariableName
    )
import Kore.Step.Simplification.OrPattern

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
    x :: TermLike RewritingVariableName
    x = mkElemVar Mock.xConfig

positive :: TermLike RewritingVariableName -> Predicate RewritingVariableName
positive u =
    makeEqualsPredicate
        (Mock.builtinBool False)
        (Mock.lessInt
            (Mock.fTestFunctionalInt u)  -- wrap the given term for sort agreement
            (Mock.builtinInt 0)
        )

negative :: TermLike RewritingVariableName -> Predicate RewritingVariableName
negative u =
    makeEqualsPredicate
        (Mock.greaterEqInt
            (Mock.fTestFunctionalInt u)  -- wrap the given term for sort agreement
            (Mock.builtinInt 0)
        )
        (Mock.builtinBool False)

runSimplifyPredicates
    :: Predicate RewritingVariableName
    -> OrPattern RewritingVariableName
    -> IO (OrPattern RewritingVariableName)
runSimplifyPredicates predicate orPattern =
    Test.runSimplifierSMT Mock.env
    $ simplifyConditionsWithSmt
        (SideCondition.assumeTruePredicate predicate)
        orPattern
