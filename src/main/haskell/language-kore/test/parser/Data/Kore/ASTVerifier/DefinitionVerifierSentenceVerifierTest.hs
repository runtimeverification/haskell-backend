module Data.Kore.ASTVerifier.DefinitionVerifierSentenceVerifierTest
    (definitionVerifierSentenceVerifierTests) where

import           Test.Tasty                                          (TestTree,
                                                                      testGroup)

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.ASTVerifier.DefinitionVerifierTestHelpers
import           Data.Kore.Error
import           Data.Kore.Implicit.ImplicitSorts

definitionVerifierSentenceVerifierTests :: TestTree
definitionVerifierSentenceVerifierTests =
    testGroup
        "Definition verifier - unique sort variables - unit tests"
        [ expectSuccess "Axiom with sort argument"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ axiomSentenceWithSortParameters
                    (asKorePattern
                        (TopPattern
                            (Top
                                { topSort =
                                    sortVariableSort (SortVariableName "#s")
                                }
                            :: Top Meta CommonKorePattern
                            )
                        )
                    )
                    [unifiedSortVariable Meta (SortVariableName "#s")]
                ]
            )
        , expectSuccess "Axiom with sort argument"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ axiomSentenceWithSortParameters
                    (asKorePattern
                        (TopPattern
                            (Top
                                { topSort =
                                    sortVariableSort (SortVariableName "#s")
                                }
                            :: Top Meta CommonKorePattern
                            )
                        )
                    )
                    [unifiedSortVariable Object (SortVariableName "s")]
                ]
            )
        , expectFailureWithError
            "Sort with undeclared sort argument"
            (Error
                ["module 'MODULE'"
                , "axiom declaration"
                , "\\top"
                , "(<test data>)"
                ]
                "Sort variable '#s1' not declared."
            )
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ axiomSentenceWithSortParameters
                    (asKorePattern
                        (TopPattern
                            (Top
                                { topSort =
                                    sortVariableSort (SortVariableName "#s1")
                                }
                            :: Top Meta CommonKorePattern
                            )
                        )
                    )
                    [unifiedSortVariable Meta (SortVariableName "#s")]
                ]
            )
        ]
