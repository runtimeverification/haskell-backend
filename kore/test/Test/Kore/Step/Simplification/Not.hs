module Test.Kore.Step.Simplification.Not
    ( test_simplifyEvaluated
    ) where

import Prelude.Kore

import Test.Tasty
    ( TestTree
    )

import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import qualified Kore.Internal.MultiOr as MultiOr
import qualified Kore.Internal.SideCondition as SideCondition
    ( top
    )
import Kore.Internal.TermLike
import qualified Kore.Step.Simplification.Not as Not
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
import Test.Kore.Internal.Predicate
    ( TestPredicate
    )
import qualified Test.Kore.Internal.Predicate as Predicate
import Test.Kore.Internal.Substitution as Substitution
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext

test_simplifyEvaluated :: [TestTree]
test_simplifyEvaluated =
    [ [Pattern.top] `becomes_` []
    , [] `becomes_` [Pattern.top]
    , [termX] `becomes_` [termNotX]
    , [termNotX] `becomes_` [termX]
    , [equalsXA] `becomes_` [notEqualsXA]
    , equalsXAWithSortedBottom `patternBecomes` [Pattern.top]
    , [substXA] `becomes_` [notEqualsXA]
    , [equalsXA, equalsXB] `becomes_` [neitherXAB]
    , [xAndEqualsXA] `becomes_` [termNotX, notEqualsXASorted]
    , [termXAndY] `becomes_` [termNotX, termNotY]
    , [termNotXAndY] `becomes_` [termX, termNotY]
    ]
  where
    becomes_
        :: HasCallStack
        => [TestPattern]
        -> [TestPattern]
        -> TestTree
    becomes_ originals expecteds =
        testCase "becomes" $ do
            actual <- simplifyEvaluated original
            let actual' = MultiOr.map (Pattern.coerceSort Mock.testSort) actual
            assertBool (message actual) (expected == actual')
      where
        original =
            OrPattern.fromPatterns
            (Pattern.coerceSort Mock.testSort <$> originals)
        expected =
            OrPattern.fromPatterns
            (Pattern.coerceSort Mock.testSort <$> expecteds)
        message actual =
            (show . Pretty.vsep)
                [ "expected simplification of:"
                , Pretty.indent 4 $ Pretty.vsep $ unparse <$> originals
                , "would give:"
                , Pretty.indent 4 $ Pretty.vsep $ unparse <$> expecteds
                , "but got:"
                , Pretty.indent 4 $ Pretty.vsep $ unparse <$> actuals
                ]
          where
            actuals = toList actual
    patternBecomes
        :: HasCallStack
        => TestPattern
        -> [TestPattern]
        -> TestTree
    patternBecomes original expecteds =
        testCase "patternBecomes" $ do
            let actuals = toList $ Not.makeEvaluate original
            assertEqual (message actuals) expecteds actuals
      where
        message actuals =
            (show . Pretty.vsep)
                [ "expected simplification of:"
                , Pretty.indent 4 $ unparse original
                , "would give:"
                , Pretty.indent 4 $ Pretty.vsep $ unparse <$> expecteds
                , "but got:"
                , Pretty.indent 4 $ Pretty.vsep $ unparse <$> actuals
                ]

termX :: TestPattern
termX = Pattern.fromTermLike (mkElemVar Mock.x)

termY :: TestPattern
termY = Pattern.fromTermLike (mkElemVar Mock.y)

termXAndY :: TestPattern
termXAndY = mkAnd <$> termX <*> termY

termNotXAndY :: TestPattern
termNotXAndY = mkAnd <$> termNotX <*> termY

termNotX :: TestPattern
termNotX = mkNot <$> termX

termNotY :: TestPattern
termNotY = mkNot <$> termY

xAndEqualsXA :: TestPattern
xAndEqualsXA = const <$> termX <*> equalsXA

equalsXAWithSortedBottom :: TestPattern
equalsXAWithSortedBottom = Conditional
    { term = mkBottom Mock.testSort
    , predicate = equalsXA_
    , substitution = mempty
    }

equalsXA :: TestPattern
equalsXA = fromPredicate equalsXA_

equalsXB :: TestPattern
equalsXB = fromPredicate equalsXB_

equalsXA_ :: TestPredicate
equalsXA_ = Predicate.makeEqualsPredicate (mkElemVar Mock.x) Mock.a

equalsXB_ :: TestPredicate
equalsXB_ = Predicate.makeEqualsPredicate (mkElemVar Mock.x) Mock.b

notEqualsXA :: TestPattern
notEqualsXA = fromPredicate $ Predicate.makeNotPredicate equalsXA_

notEqualsXASorted :: TestPattern
notEqualsXASorted =
    Pattern.coerceSort Mock.testSort notEqualsXA

neitherXAB :: TestPattern
neitherXAB =
    Pattern.coerceSort Mock.testSort
    $ fromPredicate
    $ Predicate.makeAndPredicate
        (Predicate.makeNotPredicate equalsXA_)
        (Predicate.makeNotPredicate equalsXB_)

substXA :: TestPattern
substXA = fromSubstitution $ Substitution.unsafeWrap [(inject Mock.x, Mock.a)]

forceTermSort :: TestPattern -> TestPattern
forceTermSort = fmap (forceSort Mock.testSort)

fromPredicate :: TestPredicate -> TestPattern
fromPredicate =
    forceTermSort
    . Pattern.fromCondition_
    . Condition.fromPredicate

fromSubstitution
    :: TestSubstitution
    -> TestPattern
fromSubstitution =
    forceTermSort
    . Pattern.fromCondition_
    . Condition.fromSubstitution

simplifyEvaluated
    :: OrTestPattern
    -> IO OrTestPattern
simplifyEvaluated =
    runSimplifier mockEnv . Not.simplifyEvaluated SideCondition.top
  where
    mockEnv = Mock.env
