module Test.Kore.Step.Simplification.Implies
    ( test_simplifyEvaluated
    ) where

import Prelude.Kore

import Test.Tasty
import Test.Tasty.HUnit

import Kore.Internal.Condition
    ( Condition
    , andCondition
    )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import qualified Kore.Internal.SideCondition as SideCondition
    ( top
    )
import Kore.Internal.TermLike
import qualified Kore.Step.Simplification.Implies as Implies
import Kore.Unparser
import qualified Pretty

import Test.Kore.Internal.OrPattern
    ( OrTestPattern
    )
import qualified Test.Kore.Internal.OrPattern as OrPattern
import Test.Kore.Internal.Pattern
    ( TestPattern
    )
import qualified Test.Kore.Internal.Pattern as Pattern
import Test.Kore.Internal.Predicate as Predicate
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification

test_simplifyEvaluated :: [TestTree]
test_simplifyEvaluated =
    [ ([Pattern.top], [Pattern.top]) `becomes_` [Pattern.top]
    , ([Pattern.top], []) `becomes_` []
    , ([], [Pattern.top]) `becomes_` [Pattern.top]
    , ([], []) `becomes_` [Pattern.top]

    , ([termA], [termB]) `becomes_` [aImpliesB]
    , ([equalsXA], [equalsXB]) `becomes_` [impliesEqualsXAEqualsXB]
    , ([equalsXA], [equalsXB, equalsXC])
        `becomes_` [impliesEqualsXAEqualsXB, impliesEqualsXAEqualsXC]
    , ([equalsXA, equalsXB], [equalsXC])
        `becomes_`
            [ Pattern.coerceSort Mock.testSort
                (impliesEqualsXAEqualsXC
                    `andCondition` impliesEqualsXBEqualsXC_
                )
            ]
    ]
  where
    becomes_
        :: HasCallStack
        => ([TestPattern], [TestPattern])
        -> [TestPattern]
        -> TestTree
    becomes_ (firsts, seconds) expecteds =
        testCase "becomes" $ do
            actual <- simplifyEvaluated first second
            assertEqual (message actual) expected actual
            assertBool (message actual) (expected == actual)
      where
        first = OrPattern.fromPatterns firsts
        second = OrPattern.fromPatterns seconds
        expected = OrPattern.fromPatterns expecteds
        message actual =
            (show . Pretty.vsep)
                [ "expected simplification of:"
                , Pretty.indent 4 $ Pretty.vsep $ unparse <$> firsts
                , "->"
                , Pretty.indent 4 $ Pretty.vsep $ unparse <$> seconds
                , "would give:"
                , Pretty.indent 4 $ Pretty.vsep $ unparse <$> expecteds
                , "but got:"
                , Pretty.indent 4 $ Pretty.vsep $ unparse <$> actuals
                ]
          where
            actuals = toList actual

termA :: TestPattern
termA = Pattern.fromTermLike Mock.a

termB :: TestPattern
termB = Pattern.fromTermLike Mock.b

aImpliesB :: TestPattern
aImpliesB = Conditional
    { term = mkImplies Mock.a Mock.b
    , predicate = Predicate.makeTruePredicate
    , substitution = mempty
    }

equalsXA :: TestPattern
equalsXA = Pattern.fromPredicateSorted Mock.testSort equalsXA_

equalsXB :: TestPattern
equalsXB = Pattern.fromPredicateSorted Mock.testSort equalsXB_

equalsXC :: TestPattern
equalsXC = Pattern.fromPredicateSorted Mock.testSort equalsXC_

equalsXA_ :: TestPredicate
equalsXA_ = Predicate.makeEqualsPredicate (mkElemVar Mock.x) Mock.a

equalsXB_ :: TestPredicate
equalsXB_ = Predicate.makeEqualsPredicate (mkElemVar Mock.x) Mock.b

equalsXC_ :: TestPredicate
equalsXC_ = Predicate.makeEqualsPredicate (mkElemVar Mock.x) Mock.c

impliesEqualsXAEqualsXB :: TestPattern
impliesEqualsXAEqualsXB =
    Predicate.makeImpliesPredicate equalsXA_ equalsXB_
    & Pattern.fromPredicateSorted Mock.testSort

impliesEqualsXAEqualsXC :: TestPattern
impliesEqualsXAEqualsXC =
    Predicate.makeImpliesPredicate equalsXA_ equalsXC_
    & Pattern.fromPredicateSorted Mock.testSort

impliesEqualsXBEqualsXC_ :: Condition VariableName
impliesEqualsXBEqualsXC_ =
    Predicate.makeImpliesPredicate equalsXB_ equalsXC_
    & Condition.fromPredicate

simplifyEvaluated
    :: OrTestPattern
    -> OrTestPattern
    -> IO OrTestPattern
simplifyEvaluated first second =
    runSimplifier mockEnv
    $ Implies.simplifyEvaluated SideCondition.top first second
  where
    mockEnv = Mock.env
