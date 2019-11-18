module Test.Kore.Step.Simplification.Not
    ( --t-est_simplifyEvaluated
    ) where
{-
import Test.Tasty
    ( TestTree
    )

import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified GHC.Stack as GHC

import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional
    ( Conditional (Conditional)
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
import Kore.Step.Simplification.Not
import Kore.Unification.Substitution
    ( Substitution
    )
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unparser
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty.HUnit.Ext

t-est_simplifyEvaluated :: [TestTree]
t-est_simplifyEvaluated =
    [ [Pattern.top] `becomes_` mkOr mkBottom_ mkBottom_
    , [] `becomes_` mkTop_
    , [termXP] `becomes_` mkOr termNotX mkBottom_
    , [termNotXP] `becomes_` mkOr termX mkBottom_
    , [equalsXA] `becomes_` bottomNotEqualsXA
    , equalsXAWithSortedBottom `patternBecomes` topNotEqualsXA
    , [substXA] `becomes_` bottomNotEqualsXA
    , [equalsXA, equalsXB] `becomes_` neitherXAB
    , [xAndEqualsXA] `becomes_` mkOr termNotX notEqualsXA
    , [termXAndYP] `becomes_` eitherNotXAB
    , [termNotXAndYP] `becomes_` eitherXNotY
    ]
  where
    becomes_
        :: GHC.HasCallStack
        => [Pattern Variable]
        -> TermLike Variable
        -> TestTree
    becomes_ originals expected =
        testCase "becomes" $ do
            let actual = simplifyEvaluated original
            assertBool (message actual) (expected == actual)
      where
        original = OrPattern.fromPatterns originals
        message actual =
            (show . Pretty.vsep)
                [ "expected simplification of:"
                , Pretty.indent 4 $ Pretty.vsep $ unparse <$> originals
                , "would give:"
                , Pretty.indent 4 $ unparse expected
                , "but got:"
                , Pretty.indent 4 $ unparse actual
                ]
    patternBecomes
        :: GHC.HasCallStack
        => Pattern Variable
        -> TermLike Variable
        -> TestTree
    patternBecomes original expected =
        testCase "patternBecomes" $ do
            let actual = makeEvaluate original
            assertBool (message actual) (expected == actual)
      where
        message actual =
            (show . Pretty.vsep)
                [ "expected simplification of:"
                , Pretty.indent 4 $ unparse original
                , "would give:"
                , Pretty.indent 4 $ unparse expected
                , "but got:"
                , Pretty.indent 4 $ unparse actual
                ]

termX :: TermLike Variable
termX = mkElemVar Mock.x

termXP :: Pattern Variable
termXP = Pattern.fromTermLike termX

termY :: TermLike Variable
termY = mkElemVar Mock.y

termXAndY :: TermLike Variable
termXAndY = mkAnd termX termY

termXAndYP :: Pattern Variable
termXAndYP = Pattern.fromTermLike termXAndY

termNotXAndY :: TermLike Variable
termNotXAndY = mkAnd termNotX termY

termNotXAndYP :: Pattern Variable
termNotXAndYP = Pattern.fromTermLike termNotXAndY

termNotX :: TermLike Variable
termNotX = mkNot termX

termNotXP :: Pattern Variable
termNotXP = Pattern.fromTermLike termNotX

termNotY :: TermLike Variable
termNotY = mkNot termY

xAndEqualsXA :: Pattern Variable
xAndEqualsXA = const <$> termXP <*> equalsXA

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
equalsXA_ = Predicate.makeEqualsPredicate (mkElemVar Mock.x) Mock.a

equalsXB_ :: Predicate Variable
equalsXB_ = Predicate.makeEqualsPredicate (mkElemVar Mock.x) Mock.b

notEqualsXA :: TermLike Variable
notEqualsXA = Predicate.unwrapPredicate $ Predicate.makeNotPredicate equalsXA_

topNotEqualsXA :: TermLike Variable
topNotEqualsXA = mkOr (mkTop Mock.testSort) notEqualsXA

bottomNotEqualsXA :: TermLike Variable
bottomNotEqualsXA = mkOr (mkBottom Mock.testSort) notEqualsXA

eitherNotXAB :: TermLike Variable
eitherNotXAB = mkOr (mkOr termNotX termNotY) mkBottom_

eitherXNotY :: TermLike Variable
eitherXNotY = mkOr (mkOr termX termNotY) mkBottom_

neitherXAB :: TermLike Variable
neitherXAB =
    mkAnd
        (mkOr
            (mkBottom Mock.testSort)
            (Predicate.unwrapPredicate
                (Predicate.makeNotPredicate equalsXA_)
            )
        )
        (mkOr
            mkBottom_
            (Predicate.unwrapPredicate
                (Predicate.makeNotPredicate equalsXB_)
            )
        )

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

-}
