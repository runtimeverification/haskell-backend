module Test.Kore.Step.Simplification.Not
    ( test_simplifyEvaluated
    ) where

import Prelude.Kore

import Test.Tasty
    ( TestTree
    )

import qualified Data.Foldable as Foldable

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
import Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
import qualified Kore.Step.Simplification.Not as Not
import Kore.Unparser
import qualified Pretty

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext

type Pattern' = Pattern VariableName
type OrPattern' = OrPattern VariableName
type Predicate' = Predicate VariableName
type Substitution' = Substitution VariableName

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
        => [Pattern']
        -> [Pattern']
        -> TestTree
    becomes_ originals expecteds =
        testCase "becomes" $ do
            actual <- simplifyEvaluated original
            assertBool (message actual) (expected == actual)
      where
        original = OrPattern.fromPatterns originals
        expected = OrPattern.fromPatterns expecteds
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
            actuals = Foldable.toList actual
    patternBecomes
        :: HasCallStack
        => Pattern'
        -> [Pattern']
        -> TestTree
    patternBecomes original expecteds =
        testCase "patternBecomes" $ do
            let actuals = Foldable.toList $ Not.makeEvaluate original
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

termX :: Pattern'
termX = Pattern.fromTermLike (mkElemVar Mock.x)

termY :: Pattern'
termY = Pattern.fromTermLike (mkElemVar Mock.y)

termXAndY :: Pattern'
termXAndY = mkAnd <$> termX <*> termY

termNotXAndY :: Pattern'
termNotXAndY = mkAnd <$> termNotX <*> termY

termNotX :: Pattern'
termNotX = mkNot <$> termX

termNotY :: Pattern'
termNotY = mkNot <$> termY

xAndEqualsXA :: Pattern'
xAndEqualsXA = const <$> termX <*> equalsXA

equalsXAWithSortedBottom :: Pattern'
equalsXAWithSortedBottom = Conditional
    { term = mkBottom Mock.testSort
    , predicate = equalsXA_
    , substitution = mempty
    }

equalsXA :: Pattern'
equalsXA = fromPredicate equalsXA_

equalsXB :: Pattern'
equalsXB = fromPredicate equalsXB_

equalsXA_ :: Predicate'
equalsXA_ = Predicate.makeEqualsPredicate_ (mkElemVar Mock.x) Mock.a

equalsXB_ :: Predicate'
equalsXB_ = Predicate.makeEqualsPredicate_ (mkElemVar Mock.x) Mock.b

notEqualsXA :: Pattern'
notEqualsXA = fromPredicate $ Predicate.makeNotPredicate equalsXA_

notEqualsXASorted :: Pattern'
notEqualsXASorted =
    Pattern.coerceSort Mock.testSort notEqualsXA

neitherXAB :: Pattern'
neitherXAB =
    Pattern.coerceSort Mock.testSort
    $ fromPredicate
    $ Predicate.makeAndPredicate
        (Predicate.makeNotPredicate equalsXA_)
        (Predicate.makeNotPredicate equalsXB_)

substXA :: Pattern'
substXA = fromSubstitution $ Substitution.unsafeWrap [(inject Mock.x, Mock.a)]

forceTermSort :: Pattern' -> Pattern'
forceTermSort = fmap (forceSort Mock.testSort)

fromPredicate :: Predicate' -> Pattern'
fromPredicate =
    forceTermSort
    . Pattern.fromCondition
    . Condition.fromPredicate

fromSubstitution
    :: Substitution'
    -> Pattern'
fromSubstitution =
    forceTermSort
    . Pattern.fromCondition
    . Condition.fromSubstitution

simplifyEvaluated
    :: OrPattern'
    -> IO (OrPattern')
simplifyEvaluated =
    runSimplifier mockEnv . Not.simplifyEvaluated SideCondition.top
  where
    mockEnv = Mock.env
