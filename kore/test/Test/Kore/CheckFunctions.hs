{- |
Copyright : (c) Runtime Verification, 2021
License   : BSD-3-Clause
-}
module Test.Kore.CheckFunctions (
    test_checkFunctions,
) where

import Test.Kore
import Test.Tasty (
    testCase,
 )

test_checkFunctions :: TestTree
test_checkFunctions =
    testGroup
        "checkFunctions"
        [ testCase "RHS of every equation is a function pattern." $ do
            let verifiedModule =
                    verifiedMyModule
                        Module
                            { moduleName = ModuleName "MY-MODULE"
                            , moduleSentences =
                                [ asSentence mySortDecl
                                , asSentence $ constructorDecl "a"
                                , asSentence $ constructorDecl "b"
                                , functionalAxiom "a"
                                , functionalAxiom "b"
                                ]
                            , moduleAttributes = Attributes []
                            }
                expected = ExitSuccess
                actual = _
            assertEqual "" expected actual
        , testCase "Not every equation RHS is a function pattern." $ do
            let verifiedModule =
                    verifiedModule
                        Module
                            { moduleName = ModuleName "MY-MODULE"
                            , moduleSentences = _
                            , moduleAttributes = Attributes []
                            }
                expected = ExitFailure _
                actual = _
            assertEqual "" expected actual
        ]
