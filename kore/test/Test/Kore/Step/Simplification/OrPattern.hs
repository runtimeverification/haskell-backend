module Test.Kore.Step.Simplification.OrPattern where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Kore.Internal.Conditional
                 ( Conditional (Conditional) )
import qualified Kore.Internal.Conditional as Conditional
                 ( Conditional (..) )
import qualified Kore.Internal.MultiOr as MultiOr
                 ( extractPatterns, make )
import           Kore.Internal.Pattern
                 ( Pattern )
import qualified Kore.Internal.Pattern as Pattern
                 ( top )
import           Kore.Predicate.Predicate
                 ( makeCeilPredicate, makeNotPredicate )
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import           Kore.Step.Simplification.OrPattern
                 ( filterMultiOrWithTermCeil )
import           Kore.Syntax.Variable
                 ( Variable )
import qualified SMT

import           Test.Kore
import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_orSmtSimplification :: [TestTree]
test_orSmtSimplification =
    [ testCase "bottom -> bottom" $ do
        let expected = []
        actual <- filterOr []
        assertEqualWithExplanation "" expected actual
    , testCase "top -> top" $ do
        let expected = [Pattern.top]
        actual <- filterOr [Pattern.top]
        assertEqualWithExplanation "" expected actual
    , testCase "pattern with predicate" $ do
        let
            expected =
                [ Conditional
                    { term = Mock.f Mock.a
                    , predicate = makeCeilPredicate (Mock.g Mock.a)
                    , substitution = mempty
                    }
                ]
        actual <- filterOr expected
        assertEqualWithExplanation "" expected actual
    , testCase "pattern with negated ceil" $ do
        let
            expected = []
            input =
                [ Conditional
                    { term = Mock.f Mock.a
                    , predicate =
                        makeNotPredicate (makeCeilPredicate (Mock.f Mock.a))
                    , substitution = mempty
                    }
                ]
        actual <- filterOr input
        assertEqualWithExplanation "" expected actual
    ]


filterOr
    :: [Pattern Variable]
    -> IO [Pattern Variable]
filterOr patterns =
    MultiOr.extractPatterns
    <$> SMT.runSMT SMT.defaultConfig emptyLogger
        ( evalSimplifier mockEnv
        $ filterMultiOrWithTermCeil
        $ MultiOr.make patterns
        )
  where
    mockEnv = Mock.env
