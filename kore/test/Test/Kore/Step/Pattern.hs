module Test.Kore.Step.Pattern where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Data.Sup
import Kore.AST.Common
import Kore.AST.Valid
import Kore.Step.Pattern
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

x :: Variable Object
x = Mock.x

x_0 :: Variable Object
x_0 = x { variableCounter = Just (Element 0) }

x0 :: Variable Object
x0 = x { variableName = "x0" }

x00 :: Variable Object
x00 = x { variableName = "x00" }

x1 :: Variable Object
x1 = x { variableName = "x1" }
