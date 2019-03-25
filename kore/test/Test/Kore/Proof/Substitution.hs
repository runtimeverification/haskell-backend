module Test.Kore.Proof.Substitution
    ( test_substitutions
    ) where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
       ( Assertion, assertEqual, testCase )

import           Control.Lens
import           Data.Text
                 ( Text )
import qualified Data.Text as Text

import Kore.AST.Pure
import Kore.AST.Valid
import Kore.Proof.Substitution
import Kore.Step.Pattern

test_substitutions :: TestTree
test_substitutions = testGroup "Substitutions"
    [ testCase "subTrivial" $ assertEqual "" subTrivial subTrivialSolution
    , testCase "subShadow"  $ assertEqual "" subShadow subShadowSolution
    , testCase "subAlphaRename1" $
          assertEqual ""
              subAlphaRename1
              subAlphaRename1Solution
    , testCase "subAlphaRename2" $
          assertEqual ""
              (subAlphaRename2 ^? inPath [0])
              (Just $ mkVar $ var "b")
    , testCase "subTermForTerm" $
          assertEqual ""
              subTermForTerm
              subTermForTermSolution
    , testGetSetIdentity 5
    ]

subTrivial :: CommonStepPattern Object
subTrivial =
    subst (mkVar $ var "a") (mkVar $ var "b") $
    mkExists (var "p") (mkVar $ var "a")

subTrivialSolution :: CommonStepPattern Object
subTrivialSolution = mkExists (var "p") (mkVar $ var "b")

subShadow :: CommonStepPattern Object
subShadow =
    subst (mkVar $ var "a") (mkVar $ var "b") $
    mkExists (var "a") (mkVar $ var "q")

subShadowSolution :: CommonStepPattern Object
subShadowSolution =
    mkExists (var "a") (mkVar $ var "q")

subAlphaRename1 :: CommonStepPattern Object
subAlphaRename1 =
    subst (mkVar $ var "a") (mkVar $ var "b") $
    mkExists (var "b") (mkVar $ var "q")

subAlphaRename1Solution :: CommonStepPattern Object
subAlphaRename1Solution =
    mkExists (var "b0") (mkVar $ var "q")

subAlphaRename2 :: CommonStepPattern Object
subAlphaRename2 =
    subst (mkVar $ var "a") (mkVar $ var "b") $
    mkExists (var "b") (mkVar $ var "a")

subTermForTerm :: CommonStepPattern Object
subTermForTerm =
    subst (mkOr mkTop_ mkBottom_) (mkAnd mkTop_ mkBottom_) $
    mkImplies (mkOr mkTop_ mkBottom_) mkTop_

subTermForTermSolution :: CommonStepPattern Object
subTermForTermSolution =
    mkImplies (mkAnd mkTop_ mkBottom_) mkTop_

substitutionGetSetIdentity
    :: MetaOrObject level
    => StepPattern level Variable
    -> StepPattern level Variable
    -> StepPattern level Variable
    -> Assertion
substitutionGetSetIdentity a b pat =
  assertEqual ""
    (subst b a pat)
    (subst b a $ subst a b pat)

--FIXME: Make a proper Tasty generator instead
testGetSetIdentity
  :: Int
  -> TestTree
testGetSetIdentity size = testGroup "getSetIdent" $ do
  a <- generatePatterns (size `div` 3)
  b <- generatePatterns (size `div` 3)
  pat <- generatePatterns size
  return $ testCase "" $ substitutionGetSetIdentity a b pat

generatePatterns :: Int -> [CommonStepPattern Object]
generatePatterns size = genBinaryPatterns size ++ genUnaryPatterns size

genBinaryPatterns :: Int -> [CommonStepPattern Object]
genBinaryPatterns 0 = []
genBinaryPatterns size = do
  sa <- [1..size-1]
  let sb = size - sa
  a <- generatePatterns sa
  b <- generatePatterns sb
  [mkAnd a b, mkOr a b, mkImplies a b, mkIff a b, mkRewrites a b]

genUnaryPatterns :: Int -> [CommonStepPattern Object]
genUnaryPatterns 0 = []
genUnaryPatterns 1 = [mkVar $ var_ "x" "X"]
genUnaryPatterns size = do
  a <- generatePatterns (size - 1)
  [mkNot a, mkNext a, mkForall (var $ Text.pack $ show size) a]

var :: MetaOrObject level => Text -> Variable level
var x = Variable (noLocationId x) mempty (mkSort "S")

var_ :: MetaOrObject level => Text -> Id level -> Variable level
var_ x s = Variable (noLocationId x) mempty (mkSort s)
