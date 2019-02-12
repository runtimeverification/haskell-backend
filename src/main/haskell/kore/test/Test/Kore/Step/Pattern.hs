module Test.Kore.Step.Pattern where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Control.Monad.Counter
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
            (evalCounter
                (substitute
                    (Map.singleton Mock.x (mkVar Mock.z))
                    (mkVar Mock.x)
                )
            )
        )
    , testCase "Ignores non-target variable"
        (assertEqualWithExplanation
            "Expected original non-target variable"
            (mkVar Mock.y)
            (evalCounter
                (substitute
                    (Map.singleton Mock.x (mkVar Mock.z))
                    (mkVar Mock.y)
                )
            )
        )
    , testGroup "Ignores patterns without children"
        [ testCase "Bottom"
            (assertEqualWithExplanation
                "Expected no substitution"
                (mkBottom Mock.testSort)
                (evalCounter
                    (substitute
                        (Map.singleton Mock.x (mkVar Mock.z))
                        (mkBottom Mock.testSort)
                    )
                )
            )
        , testCase "Top"
            (assertEqualWithExplanation
                "Expected no substitution"
                (mkTop Mock.testSort)
                (evalCounter
                    (substitute
                        (Map.singleton Mock.x (mkVar Mock.z))
                        (mkTop Mock.testSort)
                    )
                )
            )
        ]
    , testGroup "Ignores shadowed variables"
        [ testCase "Exists"
            (assertEqualWithExplanation
                "Expected shadowed variable to be ignored"
                (mkExists Mock.x (mkVar Mock.x))
                (evalCounter
                    (substitute
                        (Map.singleton Mock.x (mkVar Mock.z))
                        (mkExists Mock.x (mkVar Mock.x))
                    )
                )
            )
        , testCase "Forall"
            (assertEqualWithExplanation
                "Expected shadowed variable to be ignored"
                (mkForall Mock.x (mkVar Mock.x))
                (evalCounter
                    (substitute
                        (Map.singleton Mock.x (mkVar Mock.z))
                        (mkForall Mock.x (mkVar Mock.x))
                    )
                )
            )
        ]
    , testGroup "Renames quantified variables to avoid capture"
        [ testCase "Exists"
            (assertEqualWithExplanation
                "Expected quantified variable to be renamed"
                (evalCounter $ do
                    let Just z' = refreshVariable (Set.singleton Mock.z) Mock.z
                    return
                        (mkExists z'
                            (mkAnd
                                (mkVar z')
                                (mkVar Mock.z)
                            )
                        )
                )
                (evalCounter
                    (substitute
                        (Map.singleton Mock.x (mkVar Mock.z))
                        (mkExists Mock.z
                            (mkAnd
                                (mkVar Mock.z)
                                (mkVar Mock.x)
                            )
                        )
                    )
                )
            )
        , testCase "Forall"
            (assertEqualWithExplanation
                "Expected quantified variable to be renamed"
                (evalCounter $ do
                    let Just z' = refreshVariable (Set.singleton Mock.z) Mock.z
                    return
                        (mkForall z'
                            (mkAnd
                                (mkVar z')
                                (mkVar Mock.z)
                            )
                        )
                )
                (evalCounter
                    (substitute
                        (Map.singleton Mock.x (mkVar Mock.z))
                        (mkForall Mock.z
                            (mkAnd
                                (mkVar Mock.z)
                                (mkVar Mock.x)
                            )
                        )
                    )
                )
            )
        ]
    ]
