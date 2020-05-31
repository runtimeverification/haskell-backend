module Test.Kore.Step.Simplification.Implies
    ( test_simplifyEvaluated
    ) where

import Prelude.Kore

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Foldable as Foldable

import Kore.Internal.Condition
    ( Condition
    , andCondition
    )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
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
import qualified Kore.Internal.SideCondition as SideCondition
    ( top
    )
import Kore.Internal.TermLike
import qualified Kore.Step.Simplification.Implies as Implies
import Kore.Unparser
import qualified Pretty

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification

type Pattern' = Pattern VariableName
type OrPattern' = OrPattern VariableName
type Predicate' = Predicate VariableName

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
        => ([Pattern'], [Pattern'])
        -> [Pattern']
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

termA :: Pattern'
termA = Pattern.fromTermLike Mock.a

termB :: Pattern'
termB = Pattern.fromTermLike Mock.b

aImpliesB :: Pattern'
aImpliesB = Conditional
    { term = mkImplies Mock.a Mock.b
    , predicate = Predicate.makeTruePredicate_
    , substitution = mempty
    }

equalsXA :: Pattern'
equalsXA = fromPredicate equalsXA_

equalsXB :: Pattern'
equalsXB = fromPredicate equalsXB_

equalsXC :: Pattern'
equalsXC = fromPredicate equalsXC_

equalsXA_ :: Predicate'
equalsXA_ = Predicate.makeEqualsPredicate_ (mkElemVar Mock.x) Mock.a

equalsXB_ :: Predicate'
equalsXB_ = Predicate.makeEqualsPredicate_ (mkElemVar Mock.x) Mock.b

equalsXC_ :: Predicate'
equalsXC_ = Predicate.makeEqualsPredicate_ (mkElemVar Mock.x) Mock.c

impliesEqualsXAEqualsXB :: Pattern'
impliesEqualsXAEqualsXB = fromPredicate $
    Predicate.makeImpliesPredicate equalsXA_ equalsXB_

impliesEqualsXAEqualsXC :: Pattern'
impliesEqualsXAEqualsXC = fromPredicate $
    Predicate.makeImpliesPredicate equalsXA_ equalsXC_

impliesEqualsXBEqualsXC_ :: Condition VariableName
impliesEqualsXBEqualsXC_ = Condition.fromPredicate $
    Predicate.makeImpliesPredicate equalsXB_ equalsXC_

forceTermSort :: Pattern' -> Pattern'
forceTermSort = fmap (forceSort Mock.testSort)

fromPredicate :: Predicate' -> Pattern'
fromPredicate =
    forceTermSort
    . Pattern.fromCondition
    . Condition.fromPredicate

simplifyEvaluated
    :: OrPattern'
    -> OrPattern'
    -> IO (OrPattern')
simplifyEvaluated first second =
    runSimplifier mockEnv
    $ Implies.simplifyEvaluated SideCondition.top first second
  where
    mockEnv = Mock.env
