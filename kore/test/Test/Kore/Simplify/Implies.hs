module Test.Kore.Simplify.Implies (
    test_simplifyEvaluated,
) where

import Kore.Internal.Condition (
    Condition,
    andCondition,
 )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional (
    Conditional (Conditional),
 )
import qualified Kore.Internal.SideCondition as SideCondition (
    top,
 )
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import qualified Kore.Simplify.Implies as Implies
import Kore.Unparser
import Prelude.Kore
import qualified Pretty
import qualified Test.Kore.Internal.OrPattern as OrPattern
import qualified Test.Kore.Internal.Pattern as Pattern
import Test.Kore.Internal.Predicate as Predicate
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Kore.Simplify
import Test.Tasty
import Test.Tasty.HUnit

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
        `becomes_` [ Pattern.coerceSort
                        Mock.testSort
                        ( impliesEqualsXAEqualsXC
                            `andCondition` impliesEqualsXBEqualsXC_
                        )
                   ]
    ]
  where
    becomes_ ::
        HasCallStack =>
        ( [Pattern.Pattern RewritingVariableName]
        , [Pattern.Pattern RewritingVariableName]
        ) ->
        [Pattern.Pattern RewritingVariableName] ->
        TestTree
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

termA :: Pattern.Pattern RewritingVariableName
termA = Pattern.fromTermLike Mock.a

termB :: Pattern.Pattern RewritingVariableName
termB = Pattern.fromTermLike Mock.b

aImpliesB :: Pattern.Pattern RewritingVariableName
aImpliesB =
    Conditional
        { term = mkImplies Mock.a Mock.b
        , predicate = Predicate.makeTruePredicate
        , substitution = mempty
        }

equalsXA :: Pattern.Pattern RewritingVariableName
equalsXA = Pattern.fromPredicateSorted Mock.testSort equalsXA_

equalsXB :: Pattern.Pattern RewritingVariableName
equalsXB = Pattern.fromPredicateSorted Mock.testSort equalsXB_

equalsXC :: Pattern.Pattern RewritingVariableName
equalsXC = Pattern.fromPredicateSorted Mock.testSort equalsXC_

equalsXA_ :: Predicate RewritingVariableName
equalsXA_ = Predicate.makeEqualsPredicate (mkElemVar Mock.xConfig) Mock.a

equalsXB_ :: Predicate RewritingVariableName
equalsXB_ = Predicate.makeEqualsPredicate (mkElemVar Mock.xConfig) Mock.b

equalsXC_ :: Predicate RewritingVariableName
equalsXC_ = Predicate.makeEqualsPredicate (mkElemVar Mock.xConfig) Mock.c

impliesEqualsXAEqualsXB :: Pattern.Pattern RewritingVariableName
impliesEqualsXAEqualsXB =
    Predicate.makeImpliesPredicate equalsXA_ equalsXB_
        & Pattern.fromPredicateSorted Mock.testSort

impliesEqualsXAEqualsXC :: Pattern.Pattern RewritingVariableName
impliesEqualsXAEqualsXC =
    Predicate.makeImpliesPredicate equalsXA_ equalsXC_
        & Pattern.fromPredicateSorted Mock.testSort

impliesEqualsXBEqualsXC_ :: Condition RewritingVariableName
impliesEqualsXBEqualsXC_ =
    Predicate.makeImpliesPredicate equalsXB_ equalsXC_
        & Condition.fromPredicate

simplifyEvaluated ::
    OrPattern.OrPattern RewritingVariableName ->
    OrPattern.OrPattern RewritingVariableName ->
    IO (OrPattern.OrPattern RewritingVariableName)
simplifyEvaluated first second =
    runSimplifier mockEnv $
        Implies.simplifyEvaluated SideCondition.top first second
  where
    mockEnv = Mock.env
