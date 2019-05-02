module Test.Kore.Internal.TermLike where

import Test.Tasty
import Test.Tasty.HUnit

import           Control.Lens
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import           Data.Text
                 ( Text )

import Data.Sup
import Kore.AST.Lens
import Kore.Internal.TermLike
import Kore.Variables.Fresh

import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions
import           Test.Terse

test_substitute :: [TestTree]
test_substitute =
    [ testCase "Replaces target variable"
        (assertEqualWithExplanation
            "Expected substituted variable"
            (mkVar Mock.z)
            (substitute
                (Map.singleton Mock.x (mkVar Mock.z))
                (mkVar Mock.x)
            )
        )

    , testCase "Ignores non-target variable"
        (assertEqualWithExplanation
            "Expected original non-target variable"
            (mkVar Mock.y)
            (substitute
                (Map.singleton Mock.x (mkVar Mock.z))
                (mkVar Mock.y)
            )
        )

    , testGroup "Ignores patterns without children" $
        let ignoring mkPredicate =
                assertEqualWithExplanation
                    "Expected no substitution"
                    expect actual
              where
                expect = mkPredicate Mock.testSort
                actual =
                    substitute
                        (Map.singleton Mock.x (mkVar Mock.z))
                        (mkPredicate Mock.testSort)
        in
            [ testCase "Bottom" (ignoring mkBottom)
            , testCase "Top" (ignoring mkTop)
            ]

    , testGroup "Ignores shadowed variables" $
        let ignoring mkQuantifier =
                assertEqualWithExplanation
                    "Expected shadowed variable to be ignored"
                    expect actual
              where
                expect = mkQuantifier Mock.x (mkVar Mock.x)
                actual =
                    substitute
                        (Map.singleton Mock.x (mkVar Mock.z))
                        (mkQuantifier Mock.x (mkVar Mock.x))
        in
            [ testCase "Exists" (ignoring mkExists)
            , testCase "Forall" (ignoring mkForall)
            ]

    , testGroup "Renames quantified variables to avoid capture" $
        let renaming mkQuantifier =
                assertEqualWithExplanation
                    "Expected quantified variable to be renamed"
                    expect actual
              where
                expect =
                    mkQuantifier z' $ mkAnd (mkVar z') (mkVar Mock.z)
                  where
                    Just z' = refreshVariable (Set.singleton Mock.z) Mock.z
                actual =
                    substitute (Map.singleton Mock.x (mkVar Mock.z))
                    $ mkQuantifier Mock.z
                    $ mkAnd (mkVar Mock.z) (mkVar Mock.x)
        in
            [ testCase "Exists" (renaming mkExists)
            , testCase "Forall" (renaming mkForall)
            ]
    ]

test_externalizeFreshVariables :: [TestTree]
test_externalizeFreshVariables =
    [ becomes (mkVar x_0) (mkVar x0) "Append counter"
    , testGroup "No aliasing"
        [ becomes (mk (mkVar x0) (mkVar x_0)) (mk (mkVar x0) (mkVar x1)) comment
        | (mk, comment) <- binaryPatterns
        ]
    , testGroup "No capturing - Original free"
        [ becomes (mk x_0 $ mkVar x0) (mk x1 $ mkVar x0) comment
        | (mk, comment) <- quantifiers
        ]
    , testGroup "No capturing - Generated free"
        [ becomes (mk x0 $ mkVar x_0) (mk x00 $ mkVar x0) comment
        | (mk, comment) <- quantifiers
        ]
    ]
  where
    binaryPatterns =
        [ (mkAnd, "And")
        , (mkEquals_, "Equals")
        , (mkIff, "Iff")
        , (mkImplies, "Implies")
        , (mkIn_, "In")
        , (mkOr, "Or")
        , (mkRewrites, "Rewrites")
        ]
    quantifiers =
        [ (mkExists, "Exists")
        , (mkForall, "Forall")
        ]
    becomes original expected =
        equals (externalizeFreshVariables original) expected

x :: Variable
x = Mock.x

x_0 :: Variable
x_0 = x { variableCounter = Just (Element 0) }

x0 :: Variable
x0 = x { variableName = "x0" }

x00 :: Variable
x00 = x { variableName = "x00" }

x1 :: Variable
x1 = x { variableName = "x1" }

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
            ((mkBottom_ :: TermLike Variable) ^? resultSort)
            (Just (predicateSort :: Sort))
    , testCase "predicateSort.2" $
        assertEqual ""
            ((mkTop_ :: TermLike Variable) ^? resultSort)
            (Just (predicateSort :: Sort))
    , testCase "predicateSort.3" $
        assertEqual ""
            ((mkExists (var_ "a" "A") mkBottom_
                    :: TermLike Variable) ^? resultSort)
            (Just (predicateSort :: Sort))
    , testGroup "sortAgreementManySimplePatterns"
        sortAgreementManySimplePatterns
    ]

-- the a : X forces bottom : X
sortAgreement1 :: TermLike Variable
sortAgreement1 =
    mkOr (mkVar $ var_ "a" "X") mkBottom_

-- the y : Y should force everything else to be Y
sortAgreement2 :: TermLike Variable
sortAgreement2 =
    mkImplies mkBottom_ $
    mkIff
        (mkEquals_ (mkVar $ var_ "foo" "X") (mkVar $ var_ "bar" "X"))
        (mkVar $ var_ "y" "Y")

varX :: TermLike Variable
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
            (termLikeSort shouldHaveSortXOneArg)
            (mkSort "X")
    let assert2 = return $ testCase "" $ assertEqual ""
            (termLikeSort shouldHaveSortXTwoArgs)
            (mkSort "X")
    let assert3 = return $ testCase "" $ assertEqual ""
            (termLikeSort shoudlHavepredicateSortOneArg)
            predicateSort
    let assert4 = return $ testCase "" $ assertEqual ""
            (termLikeSort shouldHavepredicateSortTwoArgs)
            predicateSort
    assert1 ++ assert2 ++ assert3 ++ assert4

var :: Text -> Variable
var y = var_ y "s"

var_ :: Text -> Id -> Variable
var_ y s = Variable (noLocationId y) mempty (mkSort s)
