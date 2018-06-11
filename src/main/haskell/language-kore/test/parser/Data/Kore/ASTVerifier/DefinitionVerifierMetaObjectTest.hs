module Data.Kore.ASTVerifier.DefinitionVerifierMetaObjectTest
    (definitionVerifierMetaObjectTests) where

import           Test.Tasty                                          (TestTree,
                                                                      testGroup)

import           Data.Kore.AST.Common
import           Data.Kore.AST.Sentence
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.ASTVerifier.DefinitionVerifierTestHelpers
import           Data.Kore.Error
import           Data.Kore.Implicit.ImplicitSorts

definitionVerifierMetaObjectTests :: TestTree
definitionVerifierMetaObjectTests =
    testGroup "Meta-Object pattern interactions."
        [ expectSuccess "Object pattern with meta-pattern sort."
            (simpleDefinitionFromSentences
                (ModuleName "test")
                [ simpleAxiomSentence
                    (asKorePattern
                        (notPattern
                            patternMetaSort
                            (asKorePattern (topPattern objectSort))
                        )
                    )
                , objectSortSentence
                ]
            )
        , expectFailureWithError "Object pattern with meta-char sort."
            Error
                { errorContext =
                    [ "module 'test'", "axiom declaration", "\\not", "\\top"
                    , "(<implicitly defined entity>, <test data>)" ]
                , errorError   =
                    "Expecting meta sort '#Char{}' but got object "
                    ++ "sort 'ObjectSort{}'."
                }
            (simpleDefinitionFromSentences
                (ModuleName "test")
                [ simpleAxiomSentence
                    (asKorePattern
                        (notPattern
                            charMetaSort
                            (asKorePattern (topPattern objectSort))
                        )
                    )
                , objectSortSentence
                ]
            )
        , expectSuccess "Meta pattern with meta-pattern sort in object pattern."
            (simpleDefinitionFromSentences
                (ModuleName "test")
                [ simpleAxiomSentence
                    (asKorePattern
                        (notPattern
                            objectSort
                            (asKorePattern (topPattern patternMetaSort))
                        )
                    )
                , objectSortSentence
                ]
            )
        , expectFailureWithError
            "Meta pattern with meta-char sort in object pattern."
            Error
                { errorContext =
                    [ "module 'test'", "axiom declaration", "\\not", "\\top"
                    , "(<test data>, <implicitly defined entity>)"
                    ]
                , errorError   =
                    "Expecting object sort 'ObjectSort{}' but got meta "
                    ++ "sort '#Char{}'."
                }
            (simpleDefinitionFromSentences
                (ModuleName "test")
                [ simpleAxiomSentence
                    (asKorePattern
                        (notPattern
                            objectSort
                            (asKorePattern (topPattern charMetaSort))
                        )
                    )
                , objectSortSentence
                ]
            )
        ]
  where
    objectSortName = SortName "ObjectSort"
    objectSort :: Sort Object
    objectSort = simpleSort objectSortName
    objectSortSentence = simpleSortSentence objectSortName
    topPattern s = TopPattern Top { topSort = s }
    notPattern s p =
        NotPattern Not
            { notSort = s
            , notChild = p
            }
