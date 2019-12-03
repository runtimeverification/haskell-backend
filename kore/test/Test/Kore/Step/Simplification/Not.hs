module Test.Kore.Step.Simplification.Not
    ( test_simplifyEvaluated
    ) where

import Test.Tasty
    ( TestTree
    )

import qualified Data.Foldable as Foldable
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified GHC.Stack as GHC

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
import Kore.Internal.TermLike
import qualified Kore.Step.Simplification.Not as Not
import Kore.Unification.Substitution
    ( Substitution
    )
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unparser
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

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
        :: GHC.HasCallStack
        => [Pattern Variable]
        -> [Pattern Variable]
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
        :: GHC.HasCallStack
        => Pattern Variable
        -> [Pattern Variable]
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

termX :: Pattern Variable
termX = Pattern.fromTermLike (mkElemVar Mock.x)

termY :: Pattern Variable
termY = Pattern.fromTermLike (mkElemVar Mock.y)

termXAndY :: Pattern Variable
termXAndY = mkAnd <$> termX <*> termY

termNotXAndY :: Pattern Variable
termNotXAndY = mkAnd <$> termNotX <*> termY

termNotX :: Pattern Variable
termNotX = mkNot <$> termX

termNotY :: Pattern Variable
termNotY = mkNot <$> termY

xAndEqualsXA :: Pattern Variable
xAndEqualsXA = const <$> termX <*> equalsXA

equalsXAWithSortedBottom :: Pattern Variable
equalsXAWithSortedBottom = Conditional
    { term = mkBottom Mock.testSort
    , predicate = equalsXA_
    , substitution = mempty
    }

equalsXA :: Pattern Variable
equalsXA = fromPredicate equalsXA_

equalsXB :: Pattern Variable
equalsXB = fromPredicate equalsXB_

equalsXA_ :: Predicate Variable
equalsXA_ = Predicate.makeEqualsPredicate_ (mkElemVar Mock.x) Mock.a

equalsXB_ :: Predicate Variable
equalsXB_ = Predicate.makeEqualsPredicate_ (mkElemVar Mock.x) Mock.b

notEqualsXA :: Pattern Variable
notEqualsXA = fromPredicate $ Predicate.makeNotPredicate equalsXA_

notEqualsXASorted :: Pattern Variable
notEqualsXASorted =
    Pattern.coerceSort Mock.testSort notEqualsXA

neitherXAB :: Pattern Variable
neitherXAB =
    Pattern.coerceSort Mock.testSort
    $ fromPredicate
    $ Predicate.makeAndPredicate
        (Predicate.makeNotPredicate equalsXA_)
        (Predicate.makeNotPredicate equalsXB_)

substXA :: Pattern Variable
substXA = fromSubstitution $ Substitution.unsafeWrap [(ElemVar Mock.x, Mock.a)]

forceTermSort :: Pattern Variable -> Pattern Variable
forceTermSort = fmap (forceSort Mock.testSort)

fromPredicate :: Predicate Variable -> Pattern Variable
fromPredicate =
    forceTermSort
    . Pattern.fromCondition
    . Condition.fromPredicate

fromSubstitution
    :: Substitution Variable
    -> Pattern Variable
fromSubstitution =
    forceTermSort
    . Pattern.fromCondition
    . Condition.fromSubstitution

simplifyEvaluated
    :: OrPattern Variable
    -> IO (OrPattern Variable)
simplifyEvaluated =
    runSimplifier mockEnv . Not.simplifyEvaluated
  where
    mockEnv = Mock.env
