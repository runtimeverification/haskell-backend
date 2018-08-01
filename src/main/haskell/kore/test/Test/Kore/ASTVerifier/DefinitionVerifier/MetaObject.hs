module Test.Kore.ASTVerifier.DefinitionVerifier.MetaObject
    ( test_metaObject
    ) where

import Test.Tasty
       ( TestTree )

import Kore.AST.AstWithLocation
import Kore.AST.Common
import Kore.AST.Kore
import Kore.AST.MetaOrObject
import Kore.AST.Sentence
import Kore.Error
import Kore.Implicit.ImplicitSorts

import Test.Kore.ASTVerifier.DefinitionVerifier

test_metaObject :: [TestTree]
test_metaObject =
    [ expectSuccess "Object pattern with meta-pattern sort."
        (simpleDefinitionFromSentences
            (ModuleName "test")
            [ simpleAxiomSentence
                (asKorePattern
                    (notPattern
                        (updateAstLocation patternMetaSort AstLocationTest)
                        (asKorePattern (topPattern objectSort))
                    )
                )
            , objectSortSentence
            ]
        )
    , expectFailureWithError "Object pattern with meta-char sort."
        Error
            { errorContext =
                [ "module 'test'"
                , "axiom declaration"
                , "\\not (<test data>)"
                , "\\top (<test data>)"
                , "(<test data>, <test data>)"
                ]
            , errorError   =
                "Expecting meta sort '#Char{}' but got object "
                ++ "sort 'ObjectSort{}'."
            }
        (simpleDefinitionFromSentences
            (ModuleName "test")
            [ simpleAxiomSentence
                (asKorePattern
                    (notPattern
                        (updateAstLocation charMetaSort AstLocationTest)
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
                        (asKorePattern
                            (topPattern
                                (updateAstLocation
                                    patternMetaSort AstLocationTest
                                )
                            )
                        )
                    )
                )
            , objectSortSentence
            ]
        )
    , expectFailureWithError
        "Meta pattern with meta-char sort in object pattern."
        Error
            { errorContext =
                [ "module 'test'"
                , "axiom declaration"
                , "\\not (<test data>)"
                , "\\top (<test data>)"
                , "(<test data>, <test data>)"
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
                        (asKorePattern
                            (topPattern
                                (updateAstLocation
                                    charMetaSort AstLocationTest)
                            )
                        )
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
