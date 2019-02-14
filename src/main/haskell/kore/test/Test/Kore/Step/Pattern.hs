module Test.Kore.Step.Pattern where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Kore.AST.Valid
import Kore.Step.Pattern
import Kore.Variables.Fresh

import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

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
