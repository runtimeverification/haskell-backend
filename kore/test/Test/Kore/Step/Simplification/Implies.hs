module Test.Kore.Step.Simplification.Implies
    ( test_simplifyEvaluated
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Foldable as Foldable
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified GHC.Stack as GHC

import Kore.Internal.Condition
    ( Condition
    , andCondition
    )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
import qualified Kore.Step.Simplification.Implies as Implies

import Kore.Unparser

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
        :: GHC.HasCallStack
        => ([Pattern Variable], [Pattern Variable])
        -> [Pattern Variable]
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
            actuals = Foldable.toList actual

termA :: Pattern Variable
termA = Pattern.fromTermLike Mock.a

termB :: Pattern Variable
termB = Pattern.fromTermLike Mock.b

aImpliesB :: Pattern Variable
aImpliesB = Pattern.fromTermLikeUnsorted (mkImplies Mock.a Mock.b)

equalsXA :: Pattern Variable
equalsXA = fromPredicate equalsXA_

equalsXB :: Pattern Variable
equalsXB = fromPredicate equalsXB_

equalsXC :: Pattern Variable
equalsXC = fromPredicate equalsXC_

equalsXA_ :: Predicate Variable
equalsXA_ = Predicate.makeEqualsPredicate_ (mkElemVar Mock.x) Mock.a

equalsXB_ :: Predicate Variable
equalsXB_ = Predicate.makeEqualsPredicate_ (mkElemVar Mock.x) Mock.b

equalsXC_ :: Predicate Variable
equalsXC_ = Predicate.makeEqualsPredicate_ (mkElemVar Mock.x) Mock.c

impliesEqualsXAEqualsXB :: Pattern Variable
impliesEqualsXAEqualsXB = fromPredicate $
    Predicate.makeImpliesPredicate equalsXA_ equalsXB_

impliesEqualsXAEqualsXC :: Pattern Variable
impliesEqualsXAEqualsXC = fromPredicate $
    Predicate.makeImpliesPredicate equalsXA_ equalsXC_

impliesEqualsXBEqualsXC_ :: Condition Variable
impliesEqualsXBEqualsXC_ = Condition.fromPredicate $
    Predicate.makeImpliesPredicate equalsXB_ equalsXC_

forceTermSort :: Pattern Variable -> Pattern Variable
forceTermSort = fmap (forceSort Mock.testSort)

fromPredicate :: Predicate Variable -> Pattern Variable
fromPredicate =
    forceTermSort
    . Pattern.fromCondition
    . Condition.fromPredicate

simplifyEvaluated
    :: OrPattern Variable
    -> OrPattern Variable
    -> IO (OrPattern Variable)
simplifyEvaluated first second =
    runSimplifier mockEnv $ Implies.simplifyEvaluated first second
  where
    mockEnv = Mock.env
