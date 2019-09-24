module Test.Kore.Step.Simplification.Not
    ( test_simplifyEvaluated
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Foldable as Foldable
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified GHC.Stack as GHC

import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
import qualified Kore.Predicate.Predicate as Syntax
    ( Predicate
    )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
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

test_simplifyEvaluated :: [TestTree]
test_simplifyEvaluated =
    [ [Pattern.top] `becomes_` []
    , [] `becomes_` [Pattern.top]
    , [termX] `becomes_` [termNotX]
    , [equalsXA] `becomes_` [notEqualsXA]
    , [substXA] `becomes_` [notEqualsXA]
    , [equalsXA, equalsXB] `becomes_` [neitherXAB]
    , [xAndEqualsXA] `becomes_` [termNotX, notEqualsXA]
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

termX :: Pattern Variable
termX = Pattern.fromTermLike (mkElemVar Mock.x)

termNotX :: Pattern Variable
termNotX = mkNot <$> termX

xAndEqualsXA :: Pattern Variable
xAndEqualsXA = const <$> termX <*> equalsXA

equalsXA :: Pattern Variable
equalsXA = fromPredicate equalsXA_

equalsXB :: Pattern Variable
equalsXB = fromPredicate equalsXB_

equalsXA_ :: Syntax.Predicate Variable
equalsXA_ = Syntax.Predicate.makeEqualsPredicate (mkElemVar Mock.x) Mock.a

equalsXB_ :: Syntax.Predicate Variable
equalsXB_ = Syntax.Predicate.makeEqualsPredicate (mkElemVar Mock.x) Mock.b

notEqualsXA :: Pattern Variable
notEqualsXA = fromPredicate $ Syntax.Predicate.makeNotPredicate equalsXA_

neitherXAB :: Pattern Variable
neitherXAB =
    fromPredicate
    $ Syntax.Predicate.makeAndPredicate
        (Syntax.Predicate.makeNotPredicate equalsXA_)
        (Syntax.Predicate.makeNotPredicate equalsXB_)

substXA :: Pattern Variable
substXA = fromSubstitution $ Substitution.unsafeWrap [(ElemVar Mock.x, Mock.a)]

forceTermSort :: Pattern Variable -> Pattern Variable
forceTermSort = fmap (forceSort Mock.testSort)

fromPredicate :: Syntax.Predicate Variable -> Pattern Variable
fromPredicate =
    forceTermSort
    . Pattern.fromPredicate
    . Predicate.fromPredicate

fromSubstitution
    :: Substitution Variable
    -> Pattern Variable
fromSubstitution =
    forceTermSort
    . Pattern.fromPredicate
    . Predicate.fromSubstitution

simplifyEvaluated
    :: OrPattern Variable
    -> IO (OrPattern Variable)
simplifyEvaluated =
    runSimplifier mockEnv . Not.simplifyEvaluated
  where
    mockEnv = Mock.env
