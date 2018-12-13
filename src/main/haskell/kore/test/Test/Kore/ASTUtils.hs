{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}

module Test.Kore.ASTUtils
    ( test_substitutions
    , test_sortAgreement
    , var
    , var_
    , mkSort
    ) where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import           Control.Lens
import           Data.Text
                 ( Text )
import qualified Data.Text as Text

import Kore.AST.Lens
       ( resultSort )
import Kore.AST.Pure
import Kore.AST.Valid
import Kore.ASTUtils.Substitution
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
    ]

test_sortAgreement :: TestTree
test_sortAgreement = testGroup "Sort agreement"
    [ testCase "sortAgreement1" $
        assertEqual ""
            (sortAgreement1 ^? inPath [1])
            (Just $ mkBottom (mkSort "X"))
    , testCase "sortAgreement2.1" $
        assertEqual ""
            (sortAgreement2 ^? inPath [0])
            (Just $ mkBottom (mkSort "Y"))
    , testCase "sortAgreement2.2" $
        assertEqual ""
            (sortAgreement2 ^? (inPath [1] . resultSort ))
            (Just $ mkSort "Y")
    , testCase "predicateSort.1" $
        assertEqual ""
            ((mkBottom_ :: CommonStepPattern Object) ^? resultSort)
            (Just (predicateSort :: Sort Object))
    , testCase "predicateSort.2" $
        assertEqual ""
            ((mkTop_ :: CommonStepPattern Object) ^? resultSort)
            (Just (predicateSort :: Sort Object))
    , testCase "predicateSort.3" $
        assertEqual ""
            ((mkExists (var_ "a" "A") mkBottom_
                    :: CommonStepPattern Object) ^? resultSort)
            (Just (predicateSort :: Sort Object))
    , testGroup "sortAgreementManySimplePatterns"
        sortAgreementManySimplePatterns
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

-- subAlphaRename2Solution :: CommonStepPattern Object
-- subAlphaRename2Solution = dummyEnvironment @Object $
--   subst (mkVar $ var "a") (mkVar $ var "b") $
--   mkExists (var "b0") (mkVar $ var "b")

-- the a : X forces bottom : X
sortAgreement1 :: CommonStepPattern Object
sortAgreement1 =
    mkOr (mkVar $ var_ "a" "X") mkBottom_

-- the y : Y should force everything else to be Y
sortAgreement2 :: CommonStepPattern Object
sortAgreement2 =
    mkImplies mkBottom_ $
    mkIff
        (mkEquals_ (mkVar $ var_ "foo" "X") (mkVar $ var_ "bar" "X"))
        (mkVar $ var_ "y" "Y")

varX :: CommonStepPattern Object
varX = mkVar $ var_ "x" "X"

sortAgreementManySimplePatterns :: [TestTree]
sortAgreementManySimplePatterns = do
    flexibleZeroArg <- [mkBottom_, mkTop_]
    (a,b) <- [(varX, flexibleZeroArg), (flexibleZeroArg, varX), (varX, varX)]
    shouldHaveSortXOneArg <-
        [ mkForall (var "a") varX
        , mkExists (var "a") varX
        , mkNot varX
        , mkNext varX
        ]
    shouldHaveSortXTwoArgs <-
        [ mkAnd a b
        , mkOr a b
        , mkImplies a b
        , mkIff a b
        , mkRewrites a b
        ]
    shouldHavepredicateSortTwoArgs <-
        [ mkEquals_ a b
        , mkIn_ a b
        ]
    shoudlHavepredicateSortOneArg <-
        [ mkCeil_ a
        , mkFloor_ a
        ]
    let assert1 = return $ testCase "" $ assertEqual ""
            (getSort shouldHaveSortXOneArg)
            (mkSort "X")
    let assert2 = return $ testCase "" $ assertEqual ""
            (getSort shouldHaveSortXTwoArgs)
            (mkSort "X")
    let assert3 = return $ testCase "" $ assertEqual ""
            (getSort shoudlHavepredicateSortOneArg)
            predicateSort
    let assert4 = return $ testCase "" $ assertEqual ""
            (getSort shouldHavepredicateSortTwoArgs)
            predicateSort
    assert1 ++ assert2 ++ assert3 ++ assert4

substitutionGetSetIdentity a b pat =
  assertEqual ""
  (subst b a pat)
  (subst b a $ subst a b pat)

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

--FIXME: Make a proper Tasty generator instead
testGetSetIdentity
  :: Int
  -> TestTree
testGetSetIdentity size = testGroup "getSetIdent" $ do
  a <- generatePatterns (size `div` 3)
  b <- generatePatterns (size `div` 3)
  pat <- generatePatterns size
  return $ testCase "" $ substitutionGetSetIdentity a b pat

var :: MetaOrObject level => Text -> Variable level
var x = Variable (noLocationId x) (mkSort "S")

var_ :: MetaOrObject level => Text -> Id level -> Variable level
var_ x s = Variable (noLocationId x) (mkSort s)
