module Test.Kore.Simplify.Not (
    test_simplifyEvaluated,
) where

import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional (
    Conditional (Conditional),
 )
import qualified Kore.Internal.MultiOr as MultiOr
import qualified Kore.Internal.SideCondition as SideCondition (
    top,
 )
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import qualified Kore.Simplify.Not as Not
import Kore.Unparser
import Prelude.Kore
import qualified Pretty
import qualified Test.Kore.Internal.OrPattern as OrPattern
import qualified Test.Kore.Internal.Pattern as Pattern
import qualified Test.Kore.Internal.Predicate as Predicate
import Test.Kore.Internal.Substitution as Substitution
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Kore.Simplify
import Test.Tasty (
    TestTree,
 )
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
    becomes_ ::
        HasCallStack =>
        [Pattern.Pattern RewritingVariableName] ->
        [Pattern.Pattern RewritingVariableName] ->
        TestTree
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
    patternBecomes ::
        HasCallStack =>
        Pattern.Pattern RewritingVariableName ->
        [Pattern.Pattern RewritingVariableName] ->
        TestTree
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

termX :: Pattern.Pattern RewritingVariableName
termX = Pattern.fromTermLike (mkElemVar Mock.xConfig)

termY :: Pattern.Pattern RewritingVariableName
termY = Pattern.fromTermLike (mkElemVar Mock.yConfig)

termXAndY :: Pattern.Pattern RewritingVariableName
termXAndY = mkAnd <$> termX <*> termY

termNotXAndY :: Pattern.Pattern RewritingVariableName
termNotXAndY = mkAnd <$> termNotX <*> termY

termNotX :: Pattern.Pattern RewritingVariableName
termNotX = mkNot <$> termX

termNotY :: Pattern.Pattern RewritingVariableName
termNotY = mkNot <$> termY

xAndEqualsXA :: Pattern.Pattern RewritingVariableName
xAndEqualsXA = const <$> termX <*> equalsXA

equalsXAWithSortedBottom :: Pattern.Pattern RewritingVariableName
equalsXAWithSortedBottom =
    Conditional
        { term = mkBottom Mock.testSort
        , predicate = equalsXA_
        , substitution = mempty
        }

equalsXA :: Pattern.Pattern RewritingVariableName
equalsXA = fromPredicate equalsXA_

equalsXB :: Pattern.Pattern RewritingVariableName
equalsXB = fromPredicate equalsXB_

equalsXA_ :: Predicate.Predicate RewritingVariableName
equalsXA_ = Predicate.makeEqualsPredicate (mkElemVar Mock.xConfig) Mock.a

equalsXB_ :: Predicate.Predicate RewritingVariableName
equalsXB_ = Predicate.makeEqualsPredicate (mkElemVar Mock.xConfig) Mock.b

notEqualsXA :: Pattern.Pattern RewritingVariableName
notEqualsXA = fromPredicate $ Predicate.makeNotPredicate equalsXA_

notEqualsXASorted :: Pattern.Pattern RewritingVariableName
notEqualsXASorted =
    Pattern.coerceSort Mock.testSort notEqualsXA

neitherXAB :: Pattern.Pattern RewritingVariableName
neitherXAB =
    Pattern.coerceSort Mock.testSort $
        fromPredicate $
            Predicate.makeAndPredicate
                (Predicate.makeNotPredicate equalsXA_)
                (Predicate.makeNotPredicate equalsXB_)

substXA :: Pattern.Pattern RewritingVariableName
substXA = fromSubstitution $ Substitution.unsafeWrap [(inject Mock.xConfig, Mock.a)]

forceTermSort ::
    Pattern.Pattern RewritingVariableName ->
    Pattern.Pattern RewritingVariableName
forceTermSort = fmap (forceSort Mock.testSort)

fromPredicate ::
    Predicate.Predicate RewritingVariableName ->
    Pattern.Pattern RewritingVariableName
fromPredicate =
    forceTermSort
        . Pattern.fromCondition_
        . Condition.fromPredicate

fromSubstitution ::
    Substitution RewritingVariableName ->
    Pattern.Pattern RewritingVariableName
fromSubstitution =
    forceTermSort
        . Pattern.fromCondition_
        . Condition.fromSubstitution

simplifyEvaluated ::
    OrPattern.OrPattern RewritingVariableName ->
    IO (OrPattern.OrPattern RewritingVariableName)
simplifyEvaluated =
    runSimplifier mockEnv . Not.simplifyEvaluated SideCondition.top
  where
    mockEnv = Mock.env
