module Test.Data.Kore.ASTVerifier.DefinitionVerifier.Attributes (test_attributes) where

import           Test.Tasty                                          (TestTree)

import           Test.Data.Kore
import           Test.Data.Kore.ASTVerifier.DefinitionVerifier

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.Sentence
import           Data.Kore.Error
import           Data.Kore.Implicit.Attributes                       (attributeObjectSort)

test_attributes :: [TestTree]
test_attributes =
    [ expectSuccess "Attribute sorts and symbols visible in attributes"
        Definition
            { definitionAttributes = Attributes
                [ asObjectKorePattern (ApplicationPattern Application
                    { applicationSymbolOrAlias =
                        SymbolOrAlias
                            { symbolOrAliasConstructor = testId "strict"
                            , symbolOrAliasParams = []
                            }
                    , applicationChildren =
                        [ strictDomainValuePattern
                        , argumentPositionPattern
                        ]
                    })
                ]
            , definitionModules = []
            }
    , expectFailureWithError "Attribute sort not visible outside attributes"
        (Error
            [ "module 'M1'"
            , "axiom declaration"
            , "\\dv (<test data>)"
            , "sort 'Strict' (<test data>)"
            , "(<test data>)"
            ]
            "Sort 'Strict' not declared."
        )
        Definition
            { definitionAttributes = Attributes []
            , definitionModules =
                [ Module
                    { moduleName = ModuleName "M1"
                    , moduleSentences = [
                        asSentence
                            (SentenceAxiom
                                { sentenceAxiomParameters = []
                                , sentenceAxiomPattern =
                                    strictDomainValuePattern
                                , sentenceAxiomAttributes = Attributes []
                                }::KoreSentenceAxiom
                            )
                    ]
                    , moduleAttributes = Attributes []
                    }
                ]
            }
    , expectFailureWithError "Non-attribute sort not visible in attributes"
        (Error
            [ "module 'M1'"
            , "axiom declaration"
            , "attributes"
            , "\\equals (<test data>)"
            , "sort 'mySort' (<test data>)"
            , "(<test data>)"
            ]
            "Sort 'mySort' not declared."
        )
        Definition
            { definitionAttributes = Attributes []
            , definitionModules =
                [ Module
                    { moduleName = ModuleName "M1"
                    , moduleSentences =
                        [ asSentence
                            (SentenceAxiom
                                { sentenceAxiomParameters = []
                                , sentenceAxiomPattern =
                                    domainValuePattern mySortName
                                , sentenceAxiomAttributes = Attributes
                                    [ sortSwitchingEquals
                                        (OperandSort
                                            (attributeObjectSort
                                                AstLocationTest))
                                        (ResultSort (simpleSort mySortName))
                                        (domainValuePattern mySortName)
                                    ]
                                }::KoreSentenceAxiom
                            )
                        , asSentence
                            (SentenceSort
                                { sentenceSortName = testId "mySort"
                                , sentenceSortParameters = []
                                , sentenceSortAttributes = Attributes []
                                }::KoreSentenceSort
                            )
                        ]
                    , moduleAttributes = Attributes []
                    }
                ]
            }
    , expectFailureWithError
        "Attribute symbol not visible outside attributes"
        (Error
            [ "module 'M1'"
            , "axiom declaration"
            , "symbol or alias 'secondArgument' (<test data>)"
            , "(<test data>)"
            ]
            "Symbol 'secondArgument' not defined."
        )
        Definition
            { definitionAttributes = Attributes []
            , definitionModules =
                [ Module
                    { moduleName = ModuleName "M1"
                    , moduleSentences =
                        [ asSentence
                            (SentenceAxiom
                                { sentenceAxiomParameters = []
                                , sentenceAxiomPattern =
                                    argumentPositionPattern
                                , sentenceAxiomAttributes = Attributes []
                                }::KoreSentenceAxiom
                            )
                        , asSentence
                            (SentenceSort
                                { sentenceSortName = testId "mySort"
                                , sentenceSortParameters = []
                                , sentenceSortAttributes = Attributes []
                                }::KoreSentenceSort
                            )
                        ]
                    , moduleAttributes = Attributes []
                    }
                ]
            }
    ]
  where
    mySortName :: SortName
    mySortName = SortName "mySort"
    strictDomainValuePattern :: CommonKorePattern
    strictDomainValuePattern = domainValuePattern (SortName "Strict")
    domainValuePattern :: SortName -> CommonKorePattern
    domainValuePattern sortName =
        asKorePattern
            (DomainValuePattern DomainValue
                { domainValueSort = simpleSort sortName
                , domainValueChild =
                    asKorePattern (StringLiteralPattern (StringLiteral "asgn"))
                }
            )
    sortSwitchingEquals
        :: OperandSort Object
        -> ResultSort Object
        -> CommonKorePattern
        -> CommonKorePattern
    sortSwitchingEquals
        (OperandSort operandSort) (ResultSort resultSort) child
      =
        asKorePattern
            (EqualsPattern Equals
                { equalsOperandSort = operandSort
                , equalsResultSort = resultSort
                , equalsFirst = child
                , equalsSecond = child
                }
            )
    argumentPositionPattern :: CommonKorePattern
    argumentPositionPattern =
        asObjectKorePattern
            (ApplicationPattern Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = testId "secondArgument"
                        , symbolOrAliasParams = []
                        }
                , applicationChildren = []
                }
            )
