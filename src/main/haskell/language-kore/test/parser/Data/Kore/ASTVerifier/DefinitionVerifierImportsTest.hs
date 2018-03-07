module Data.Kore.ASTVerifier.DefinitionVerifierImportsTest
    (definitionVerifierImportsTests) where

import           Test.Tasty                                          (TestTree,
                                                                      testGroup)

import           Data.Kore.AST
import           Data.Kore.ASTVerifier.DefinitionVerifierTestHelpers
import           Data.Kore.Error
import           Data.Kore.ImplicitDefinitions

definitionVerifierImportsTests :: TestTree
definitionVerifierImportsTests =
    testGroup
        "Definition verifier - imports - unit tests"
        [ importTests
        , nameVisibilityTests
        , nameDuplicationTests
        ]

importTests :: TestTree
importTests =
    testGroup
        "Module imports"
        [ expectSuccess "Simplest definition"
            Definition
                { definitionAttributes = Attributes []
                , definitionModules =
                    [ Module
                        { moduleName = ModuleName "M1"
                        , moduleSentences = []
                        , moduleAttributes = Attributes []
                        }
                    ]
                }
        , expectSuccess "Two modules"
            Definition
                { definitionAttributes = Attributes []
                , definitionModules =
                    [ Module
                        { moduleName = ModuleName "M1"
                        , moduleSentences = []
                        , moduleAttributes = Attributes []
                        }
                    , Module
                        { moduleName = ModuleName "M2"
                        , moduleSentences = []
                        , moduleAttributes = Attributes []
                        }
                    ]
                }
        , expectSuccess "Two modules with import"
            Definition
                { definitionAttributes = Attributes []
                , definitionModules =
                    [ Module
                        { moduleName = ModuleName "M1"
                        , moduleSentences = [ importSentence (ModuleName "M2") ]
                        , moduleAttributes = Attributes []
                        }
                    , Module
                        { moduleName = ModuleName "M2"
                        , moduleSentences = []
                        , moduleAttributes = Attributes []
                        }
                    ]
                }
        , expectSuccess "Three modules with chain import"
            Definition
                { definitionAttributes = Attributes []
                , definitionModules =
                    [ Module
                        { moduleName = ModuleName "M1"
                        , moduleSentences = [ importSentence (ModuleName "M2") ]
                        , moduleAttributes = Attributes []
                        }
                    , Module
                        { moduleName = ModuleName "M2"
                        , moduleSentences = [ importSentence (ModuleName "M3") ]
                        , moduleAttributes = Attributes []
                        }
                    , Module
                        { moduleName = ModuleName "M3"
                        , moduleSentences = []
                        , moduleAttributes = Attributes []
                        }
                    ]
                }
        , expectSuccess "Three modules with dag import"
            Definition
                { definitionAttributes = Attributes []
                , definitionModules =
                    [ Module
                        { moduleName = ModuleName "M1"
                        , moduleSentences =
                            [ importSentence (ModuleName "M2")
                            , importSentence (ModuleName "M3")
                            ]
                        , moduleAttributes = Attributes []
                        }
                    , Module
                        { moduleName = ModuleName "M2"
                        , moduleSentences = [ importSentence (ModuleName "M3") ]
                        , moduleAttributes = Attributes []
                        }
                    , Module
                        { moduleName = ModuleName "M3"
                        , moduleSentences = []
                        , moduleAttributes = Attributes []
                        }
                    ]
                }
        , expectFailureWithError "Circular import"
            (Error
                [ "module 'M1'", "module 'M2'", "module 'M3'", "module 'M2'" ]
                "Circular module import dependency."
            )
            Definition
                { definitionAttributes = Attributes []
                , definitionModules =
                    [ Module
                        { moduleName = ModuleName "M1"
                        , moduleSentences = [ importSentence (ModuleName "M2") ]
                        , moduleAttributes = Attributes []
                        }
                    , Module
                        { moduleName = ModuleName "M2"
                        , moduleSentences = [ importSentence (ModuleName "M3") ]
                        , moduleAttributes = Attributes []
                        }
                    , Module
                        { moduleName = ModuleName "M3"
                        , moduleSentences = [ importSentence (ModuleName "M2") ]
                        , moduleAttributes = Attributes []
                        }
                    ]
                }
        ]


nameVisibilityTests :: TestTree
nameVisibilityTests =
    testGroup
        "Name visibility though module imports"
        (  sortVisibilityTests
        ++ symbolVisibilityTests
        ++ aliasVisibilityTests
        )


sortVisibilityTests :: [TestTree]
sortVisibilityTests =
    [ nameReferenceTests
        "Sort visibility in sorts"
        (ExpectedErrorMessage "Sort 'sort1' not declared.")
        (ErrorStack
            [ "axiom declaration"
            , "\\top"
            , "sort 'sort2'"
            , "sort 'sort1'"
            ]
        )
        (DeclaringSentence sortDeclaration)
        (UsingSentence sortReferenceInSortSentence)
        (SupportingSentences sortReferenceInSortSupportingSentences)
    , nameReferenceTests
        "Sort visibility in top pattern"
        (ExpectedErrorMessage "Sort 'sort1' not declared.")
        (ErrorStack
            [ "axiom declaration"
            , "\\top"
            , "sort 'sort1'"
            ]
        )
        (DeclaringSentence sortDeclaration)
        (UsingSentence sortReferenceInTopPatternSentence)
        (SupportingSentences [])
    , nameReferenceTests
        "Sort visibility in exists pattern"
        (ExpectedErrorMessage "Sort 'sort1' not declared.")
        (ErrorStack
            [ "axiom declaration"
            , "\\exists 'var'"
            , "sort 'sort1'"
            ]
        )
        (DeclaringSentence sortDeclaration)
        (UsingSentence sortReferenceInExistsPatternSentence)
        (SupportingSentences [])
    , nameReferenceTests
        "Sort visibility in and pattern"
        (ExpectedErrorMessage "Sort 'sort1' not declared.")
        (ErrorStack
            [ "axiom declaration"
            , "\\and"
            , "sort 'sort1'"
            ]
        )
        (DeclaringSentence sortDeclaration)
        (UsingSentence sortReferenceInAndPatternSentence)
        (SupportingSentences [])
    , nameReferenceTests
        "Sort visibility in next pattern"
        (ExpectedErrorMessage "Sort 'sort1' not declared.")
        (ErrorStack
            [ "axiom declaration"
            , "\\next"
            , "sort 'sort1'"
            ]
        )
        (DeclaringSentence sortDeclaration)
        (UsingSentence sortReferenceInNextPatternSentence)
        (SupportingSentences [])
    , nameReferenceTests
        "Sort visibility in pattern in pattern"
        (ExpectedErrorMessage "Sort 'sort1' not declared.")
        (ErrorStack
            [ "axiom declaration"
            , "\\next"
            , "\\equals"
            , "sort 'sort1'"
            ]
        )
        (DeclaringSentence sortDeclaration)
        (UsingSentence sortReferenceInPatternInPatternSentence)
        (SupportingSentences
            sortReferenceInPatternInPatternSupportingSentences)
    , nameReferenceTests
        "Sort visibility in symbol declaration - return sort"
        (ExpectedErrorMessage "Sort 'sort1' not declared.")
        (ErrorStack
            [ "symbol 'symbol1' declaration"
            , "sort 'sort1'"
            ]
        )
        (DeclaringSentence sortDeclaration)
        (UsingSentence sortReferenceInSentenceSymbolResultSortSentence)
        (SupportingSentences [])
    , nameReferenceTests
        "Sort visibility in symbol declaration - operand sort"
        (ExpectedErrorMessage "Sort 'sort1' not declared.")
        (ErrorStack
            [ "symbol 'symbol1' declaration"
            , "sort 'sort1'"
            ]
        )
        (DeclaringSentence sortDeclaration)
        (UsingSentence sortReferenceInSentenceSymbolSortsSentence)
        (SupportingSentences
            sortReferenceInSentenceSymbolSortsSupportSentences)
    , nameReferenceTests
        "Sort visibility in alias declaration - return sort"
        (ExpectedErrorMessage "Sort 'sort1' not declared.")
        (ErrorStack
            [ "alias 'alias1' declaration"
            , "sort 'sort1'"
            ]
        )
        (DeclaringSentence sortDeclaration)
        (UsingSentence sortReferenceInSentenceAliasResultSortSentence)
        (SupportingSentences [])
    , nameReferenceTests
        "Sort visibility in alias declaration - operand sort"
        (ExpectedErrorMessage "Sort 'sort1' not declared.")
        (ErrorStack
            [ "alias 'alias1' declaration"
            , "sort 'sort1'"
            ]
        )
        (DeclaringSentence sortDeclaration)
        (UsingSentence sortReferenceInSentenceAliasSortsSentence)
        (SupportingSentences
            sortReferenceInSentenceAliasSortsSupportSentences)
    , nameReferenceTests
        "Sort visibility in application patterns"
        (ExpectedErrorMessage "Sort 'sort1' not declared.")
        (ErrorStack
            [ "axiom declaration"
            , "symbol or alias 'symbol2'"
            , "sort 'sort1'"
            ]
        )
        (DeclaringSentence sortDeclaration)
        (UsingSentence sortReferenceInSymbolOrAliasSentence)
        (SupportingSentences sortReferenceInSymbolOrAliasSupportSentences)
    , testGroup
        "Meta sort visibility in top pattern"
        (nameReferenceSuccessTests
            -- N.B., this is not related to the used sort.
            (DeclaringSentence sortDeclaration)
            (UsingSentence metaSortReferenceInTopPatternSentence)
            (SupportingSentences [])
        )
    ]
  where
    sort = SortActualSort SortActual
        { sortActualName = Id "sort1"
        , sortActualSorts = []
        }
    sortDeclaration = SentenceSortSentence SentenceSort
        { sentenceSortName = Id "sort1"
        , sentenceSortParameters = []
        , sentenceSortAttributes = Attributes []
        }
    anotherSort = SortActualSort SortActual
        { sortActualName = Id "sort3"
        , sortActualSorts = []
        }
    anotherSortDeclaration = SentenceSortSentence SentenceSort
        { sentenceSortName = Id "sort3"
        , sentenceSortParameters = []
        , sentenceSortAttributes = Attributes []
        }
    topSortPattern = ObjectPattern ( TopPattern Top { topSort = sort } )
    metaTopSortPattern =
        MetaPattern ( TopPattern Top { topSort = charMetaSort } )
    sortReferenceInSort =
        SortActualSort SortActual
            { sortActualName = Id "sort2"
            , sortActualSorts = [ sort ]
            }
    sortReferenceInSortSentence =
        SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = []
            , sentenceAxiomPattern = ObjectPattern
                ( TopPattern Top { topSort = sortReferenceInSort } )
            , sentenceAxiomAttributes = Attributes []
            }
    sortReferenceInSortSupportingSentences =
        [ SentenceSortSentence SentenceSort
            { sentenceSortName = Id "sort2"
            , sentenceSortParameters = [SortVariable (Id "x")]
            , sentenceSortAttributes = Attributes []
            }
        ]
    sortReferenceInTopPatternSentence =
        SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = []
            , sentenceAxiomPattern = topSortPattern
            , sentenceAxiomAttributes = Attributes []
            }
    metaSortReferenceInTopPatternSentence =
        SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = []
            , sentenceAxiomPattern = metaTopSortPattern
            , sentenceAxiomAttributes = Attributes []
            }
    sortReferenceInExistsPatternSentence =
        SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = []
            , sentenceAxiomPattern = ObjectPattern
                ( ExistsPattern Exists
                    { existsSort = sort
                    , existsVariable = Variable
                        { variableName = Id "var"
                        , variableSort = sort
                        }
                    , existsChild = ObjectPattern
                        ( VariablePattern Variable
                            { variableName = Id "var"
                            , variableSort = sort
                            }
                        )
                    }
                )
            , sentenceAxiomAttributes = Attributes []
            }
    sortReferenceInAndPatternSentence =
        SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = []
            , sentenceAxiomPattern = ObjectPattern
                ( AndPattern And
                    { andSort = sort
                    , andFirst = topSortPattern
                    , andSecond = topSortPattern
                    }
                )
            , sentenceAxiomAttributes = Attributes []
            }
    sortReferenceInNextPatternSentence =
        SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = []
            , sentenceAxiomPattern = ObjectPattern
                ( NextPattern Next
                    { nextSort = sort
                    , nextChild = topSortPattern
                    }
                )
            , sentenceAxiomAttributes = Attributes []
            }
    sortReferenceInPatternInPatternSentence =
        SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = []
            , sentenceAxiomPattern = ObjectPattern
                ( NextPattern Next
                    { nextSort = anotherSort
                    , nextChild = ObjectPattern
                        ( EqualsPattern Equals
                            { equalsResultSort = anotherSort
                            , equalsOperandSort = sort
                            , equalsFirst = topSortPattern
                            , equalsSecond = topSortPattern
                            }
                        )
                    }
                )
            , sentenceAxiomAttributes = Attributes []
            }
    sortReferenceInPatternInPatternSupportingSentences =
        [ anotherSortDeclaration ]
    sortReferenceInSentenceSymbolResultSortSentence =
        ObjectSentenceSymbolSentence SentenceSymbol
            { sentenceSymbolSymbol = Symbol
                { symbolConstructor = Id "symbol1"
                , symbolParams = []
                }
            , sentenceSymbolSorts = []
            , sentenceSymbolResultSort = sort
            , sentenceSymbolAttributes = Attributes []
            }
    sortReferenceInSentenceSymbolSortsSentence =
        ObjectSentenceSymbolSentence SentenceSymbol
            { sentenceSymbolSymbol = Symbol
                { symbolConstructor = Id "symbol1"
                , symbolParams = []
                }
            , sentenceSymbolSorts = [sort]
            , sentenceSymbolResultSort = anotherSort
            , sentenceSymbolAttributes = Attributes []
            }
    sortReferenceInSentenceSymbolSortsSupportSentences =
        [ anotherSortDeclaration ]
    sortReferenceInSentenceAliasResultSortSentence =
        ObjectSentenceAliasSentence SentenceAlias
            { sentenceAliasAlias = Alias
                { aliasConstructor = Id "alias1"
                , aliasParams = []
                }
            , sentenceAliasSorts = []
            , sentenceAliasResultSort = sort
            , sentenceAliasAttributes = Attributes []
            }
    sortReferenceInSentenceAliasSortsSentence =
        ObjectSentenceAliasSentence SentenceAlias
            { sentenceAliasAlias = Alias
                { aliasConstructor = Id "alias1"
                , aliasParams = []
                }
            , sentenceAliasSorts = [sort]
            , sentenceAliasResultSort = anotherSort
            , sentenceAliasAttributes = Attributes []
            }
    sortReferenceInSentenceAliasSortsSupportSentences =
        [ anotherSortDeclaration ]
    sortReferenceInSymbolOrAliasSentence =
        SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = []
            , sentenceAxiomPattern = ObjectPattern
                ( ApplicationPattern Application
                    { applicationSymbolOrAlias = SymbolOrAlias
                        { symbolOrAliasConstructor = Id "symbol2"
                        , symbolOrAliasParams = [ sort ]
                        }
                    , applicationChildren = []
                    }
                )
            , sentenceAxiomAttributes = Attributes []
            }
    sortReferenceInSymbolOrAliasSupportSentences =
        [ ObjectSentenceSymbolSentence SentenceSymbol
            { sentenceSymbolSymbol = Symbol
                { symbolConstructor = Id "symbol2"
                , symbolParams = [SortVariable (Id "sv1")]
                }
            , sentenceSymbolSorts = []
            , sentenceSymbolResultSort =
                SortVariableSort (SortVariable (Id "sv1"))
            , sentenceSymbolAttributes = Attributes []
            }
        ]

symbolVisibilityTests :: [TestTree]
symbolVisibilityTests =
    [ nameReferenceTests
        "Symbol visibility in axioms"
        (ExpectedErrorMessage "Symbol 'symbol1' not defined.")
        (ErrorStack
            [ "axiom declaration"
            , "symbol or alias 'symbol1'"
            ]
        )
        (DeclaringSentence symbolDeclaration)
        (UsingSentence symbolReferenceInAxiomSentence)
        (SupportingSentences defaultSymbolSupportSentences)
    , nameReferenceTests
        "Symbol visibility in attributes"
        (ExpectedErrorMessage "Symbol 'symbol1' not defined.")
        (ErrorStack
            [ "sort 'sort2' declaration"
            , "attributes"
            , "symbol or alias 'symbol1'"
            ]
        )
        (DeclaringSentence symbolDeclaration)
        (UsingSentence symbolReferenceInAttributesSentence)
        (SupportingSentences defaultSymbolSupportSentences)
    , nameReferenceTests
        "Symbol visibility in and pattern"
        (ExpectedErrorMessage "Symbol 'symbol1' not defined.")
        (ErrorStack
            [ "axiom declaration"
            , "\\and"
            , "symbol or alias 'symbol1'"
            ]
        )
        (DeclaringSentence symbolDeclaration)
        (UsingSentence symbolReferenceInAndPatternSentence)
        (SupportingSentences defaultSymbolSupportSentences)
    , nameReferenceTests
        "Symbol visibility in exists pattern"
        (ExpectedErrorMessage "Symbol 'symbol1' not defined.")
        (ErrorStack
            [ "axiom declaration"
            , "\\exists 'var'"
            , "symbol or alias 'symbol1'"
            ]
        )
        (DeclaringSentence symbolDeclaration)
        (UsingSentence symbolReferenceInExistsPatternSentence)
        (SupportingSentences defaultSymbolSupportSentences)
    , nameReferenceTests
        "Symbol visibility in next pattern"
        (ExpectedErrorMessage "Symbol 'symbol1' not defined.")
        (ErrorStack
            [ "axiom declaration"
            , "\\next"
            , "symbol or alias 'symbol1'"
            ]
        )
        (DeclaringSentence symbolDeclaration)
        (UsingSentence symbolReferenceInNextPatternSentence)
        (SupportingSentences defaultSymbolSupportSentences)
    , nameReferenceTests
        "Symbol visibility in application pattern"
        (ExpectedErrorMessage "Symbol 'symbol1' not defined.")
        (ErrorStack
            [ "axiom declaration"
            , "symbol or alias 'symbol2'"
            , "symbol or alias 'symbol1'"
            ]
        )
        (DeclaringSentence symbolDeclaration)
        (UsingSentence symbolReferenceInSymbolOrAliasSentence)
        (SupportingSentences symbolReferenceInSymbolOrAliasSupportSentences)
    , nameReferenceTests
        "Meta symbol visibility in axioms"
        (ExpectedErrorMessage "Symbol '#symbol1' not defined.")
        (ErrorStack
            [ "axiom declaration"
            , "symbol or alias '#symbol1'"
            ]
        )
        (DeclaringSentence metaSymbolDeclaration)
        (UsingSentence metaSymbolReferenceInAxiomSentence)
        (SupportingSentences [])
    ]
  where
    topSortPattern = ObjectPattern ( TopPattern Top { topSort = defaultSort } )
    symbolPattern = ObjectPattern
        ( ApplicationPattern Application
            { applicationSymbolOrAlias = SymbolOrAlias
                { symbolOrAliasConstructor = Id "symbol1"
                , symbolOrAliasParams = [ defaultSort ]
                }
            , applicationChildren = []
            }
        )
    symbolDeclaration = ObjectSentenceSymbolSentence SentenceSymbol
        { sentenceSymbolSymbol = Symbol
            { symbolConstructor = Id "symbol1"
            , symbolParams = [SortVariable (Id "sv1")]
            }
        , sentenceSymbolSorts = []
        , sentenceSymbolResultSort =
            SortVariableSort (SortVariable (Id "sv1"))
        , sentenceSymbolAttributes = Attributes []
        }
    defaultSymbolSupportSentences = [ defaultSortDeclaration ]
    metaSymbolPattern = MetaPattern
        ( ApplicationPattern Application
            { applicationSymbolOrAlias = SymbolOrAlias
                { symbolOrAliasConstructor = Id "#symbol1"
                , symbolOrAliasParams = [ charMetaSort ]
                }
            , applicationChildren = []
            }
        )
    metaSymbolDeclaration = MetaSentenceSymbolSentence SentenceSymbol
        { sentenceSymbolSymbol = Symbol
            { symbolConstructor = Id "#symbol1"
            , symbolParams = [SortVariable (Id "#sv1")]
            }
        , sentenceSymbolSorts = []
        , sentenceSymbolResultSort =
            SortVariableSort (SortVariable (Id "#sv1"))
        , sentenceSymbolAttributes = Attributes []
        }
    symbolReferenceInAxiomSentence =
        SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = []
            , sentenceAxiomPattern = symbolPattern
            , sentenceAxiomAttributes = Attributes []
            }
    metaSymbolReferenceInAxiomSentence =
        SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = []
            , sentenceAxiomPattern = metaSymbolPattern
            , sentenceAxiomAttributes = Attributes []
            }
    symbolReferenceInAttributesSentence =
        SentenceSortSentence SentenceSort
            { sentenceSortName = Id "sort2"
            , sentenceSortParameters = []
            , sentenceSortAttributes = Attributes [symbolPattern]
            }
    symbolReferenceInAndPatternSentence =
        SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = []
            , sentenceAxiomPattern = ObjectPattern
                ( AndPattern And
                    { andSort = defaultSort
                    , andFirst = symbolPattern
                    , andSecond = topSortPattern
                    }
                )
            , sentenceAxiomAttributes = Attributes []
            }
    symbolReferenceInExistsPatternSentence =
        SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = []
            , sentenceAxiomPattern = ObjectPattern
                ( ExistsPattern Exists
                    { existsSort = defaultSort
                    , existsVariable = Variable
                        { variableName = Id "var"
                        , variableSort = defaultSort
                        }
                    , existsChild = symbolPattern
                    }
                )
            , sentenceAxiomAttributes = Attributes []
            }
    symbolReferenceInNextPatternSentence =
        SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = []
            , sentenceAxiomPattern = ObjectPattern
                ( NextPattern Next
                    { nextSort = defaultSort
                    , nextChild = symbolPattern
                    }
                )
            , sentenceAxiomAttributes = Attributes []
            }
    symbolReferenceInSymbolOrAliasSentence =
        SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = []
            , sentenceAxiomPattern = ObjectPattern
                ( ApplicationPattern Application
                    { applicationSymbolOrAlias = SymbolOrAlias
                        { symbolOrAliasConstructor = Id "symbol2"
                        , symbolOrAliasParams = [ defaultSort ]
                        }
                    , applicationChildren = [symbolPattern]
                    }
                )
            , sentenceAxiomAttributes = Attributes []
            }
    symbolReferenceInSymbolOrAliasSupportSentences =
        ObjectSentenceSymbolSentence SentenceSymbol
            { sentenceSymbolSymbol = Symbol
                { symbolConstructor = Id "symbol2"
                , symbolParams = [SortVariable (Id "sv1")]
                }
            , sentenceSymbolSorts =
                [ SortVariableSort (SortVariable (Id "sv1")) ]
            , sentenceSymbolResultSort =
                SortVariableSort (SortVariable (Id "sv1"))
            , sentenceSymbolAttributes = Attributes []
            }
        : defaultSymbolSupportSentences

aliasVisibilityTests :: [TestTree]
aliasVisibilityTests =
    [ nameReferenceTests
        "Alias visibility in axioms"
        (ExpectedErrorMessage "Symbol 'alias1' not defined.")
        (ErrorStack
            [ "axiom declaration"
            , "symbol or alias 'alias1'"
            ]
        )
        (DeclaringSentence aliasDeclaration)
        (UsingSentence aliasReferenceInAxiomSentence)
        (SupportingSentences defaultAliasSupportSentences)
    , nameReferenceTests
        "Alias visibility in attributes"
        (ExpectedErrorMessage "Symbol 'alias1' not defined.")
        (ErrorStack
            [ "sort 'sort2' declaration"
            , "attributes"
            , "symbol or alias 'alias1'"
            ]
        )
        (DeclaringSentence aliasDeclaration)
        (UsingSentence aliasReferenceInAttributesSentence)
        (SupportingSentences defaultAliasSupportSentences)
    , nameReferenceTests
        "Alias visibility in and pattern"
        (ExpectedErrorMessage "Symbol 'alias1' not defined.")
        (ErrorStack
            [ "axiom declaration"
            , "\\and"
            , "symbol or alias 'alias1'"
            ]
        )
        (DeclaringSentence aliasDeclaration)
        (UsingSentence aliasReferenceInAndPatternSentence)
        (SupportingSentences defaultAliasSupportSentences)
    , nameReferenceTests
        "Alias visibility in exists pattern"
        (ExpectedErrorMessage "Symbol 'alias1' not defined.")
        (ErrorStack
            [ "axiom declaration"
            , "\\exists 'var'"
            , "symbol or alias 'alias1'"
            ]
        )
        (DeclaringSentence aliasDeclaration)
        (UsingSentence aliasReferenceInExistsPatternSentence)
        (SupportingSentences defaultAliasSupportSentences)
    , nameReferenceTests
        "Alias visibility in next pattern"
        (ExpectedErrorMessage "Symbol 'alias1' not defined.")
        (ErrorStack
            [ "axiom declaration"
            , "\\next"
            , "symbol or alias 'alias1'"
            ]
        )
        (DeclaringSentence aliasDeclaration)
        (UsingSentence aliasReferenceInNextPatternSentence)
        (SupportingSentences defaultAliasSupportSentences)
    , nameReferenceTests
        "Alias visibility in application pattern"
        (ExpectedErrorMessage "Symbol 'alias1' not defined.")
        (ErrorStack
            [ "axiom declaration"
            , "symbol or alias 'alias2'"
            , "symbol or alias 'alias1'"
            ]
        )
        (DeclaringSentence aliasDeclaration)
        (UsingSentence aliasReferenceInAliasOrAliasSentence)
        (SupportingSentences aliasReferenceInAliasOrAliasSupportSentences)
    , nameReferenceTests
        "Meta alias visibility in axioms"
        (ExpectedErrorMessage "Symbol '#alias1' not defined.")
        (ErrorStack
            [ "axiom declaration"
            , "symbol or alias '#alias1'"
            ]
        )
        (DeclaringSentence metaAliasDeclaration)
        (UsingSentence metaAliasReferenceInAxiomSentence)
        (SupportingSentences [])
    ]
  where
    topSortPattern = ObjectPattern ( TopPattern Top { topSort = defaultSort } )
    aliasPattern = ObjectPattern
        ( ApplicationPattern Application
            { applicationSymbolOrAlias = SymbolOrAlias
                { symbolOrAliasConstructor = Id "alias1"
                , symbolOrAliasParams = [ defaultSort ]
                }
            , applicationChildren = []
            }
        )
    aliasDeclaration = ObjectSentenceAliasSentence SentenceAlias
        { sentenceAliasAlias = Alias
            { aliasConstructor = Id "alias1"
            , aliasParams = [SortVariable (Id "sv1")]
            }
        , sentenceAliasSorts = []
        , sentenceAliasResultSort =
            SortVariableSort (SortVariable (Id "sv1"))
        , sentenceAliasAttributes = Attributes []
        }
    defaultAliasSupportSentences = [ defaultSortDeclaration ]
    metaAliasPattern = MetaPattern
        ( ApplicationPattern Application
            { applicationSymbolOrAlias = SymbolOrAlias
                { symbolOrAliasConstructor = Id "#alias1"
                , symbolOrAliasParams = [ charMetaSort ]
                }
            , applicationChildren = []
            }
        )
    metaAliasDeclaration = MetaSentenceAliasSentence SentenceAlias
        { sentenceAliasAlias = Alias
            { aliasConstructor = Id "#alias1"
            , aliasParams = [SortVariable (Id "#sv1")]
            }
        , sentenceAliasSorts = []
        , sentenceAliasResultSort =
            SortVariableSort (SortVariable (Id "#sv1"))
        , sentenceAliasAttributes = Attributes []
        }
    aliasReferenceInAxiomSentence =
        SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = []
            , sentenceAxiomPattern = aliasPattern
            , sentenceAxiomAttributes = Attributes []
            }
    metaAliasReferenceInAxiomSentence =
        SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = []
            , sentenceAxiomPattern = metaAliasPattern
            , sentenceAxiomAttributes = Attributes []
            }
    aliasReferenceInAttributesSentence =
        SentenceSortSentence SentenceSort
            { sentenceSortName = Id "sort2"
            , sentenceSortParameters = []
            , sentenceSortAttributes = Attributes [aliasPattern]
            }
    aliasReferenceInAndPatternSentence =
        SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = []
            , sentenceAxiomPattern = ObjectPattern
                ( AndPattern And
                    { andSort = defaultSort
                    , andFirst = aliasPattern
                    , andSecond = topSortPattern
                    }
                )
            , sentenceAxiomAttributes = Attributes []
            }
    aliasReferenceInExistsPatternSentence =
        SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = []
            , sentenceAxiomPattern = ObjectPattern
                ( ExistsPattern Exists
                    { existsSort = defaultSort
                    , existsVariable = Variable
                        { variableName = Id "var"
                        , variableSort = defaultSort
                        }
                    , existsChild = aliasPattern
                    }
                )
            , sentenceAxiomAttributes = Attributes []
            }
    aliasReferenceInNextPatternSentence =
        SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = []
            , sentenceAxiomPattern = ObjectPattern
                ( NextPattern Next
                    { nextSort = defaultSort
                    , nextChild = aliasPattern
                    }
                )
            , sentenceAxiomAttributes = Attributes []
            }
    aliasReferenceInAliasOrAliasSentence =
        SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = []
            , sentenceAxiomPattern = ObjectPattern
                ( ApplicationPattern Application
                    { applicationSymbolOrAlias = SymbolOrAlias
                        { symbolOrAliasConstructor = Id "alias2"
                        , symbolOrAliasParams = [ defaultSort ]
                        }
                    , applicationChildren = [aliasPattern]
                    }
                )
            , sentenceAxiomAttributes = Attributes []
            }
    aliasReferenceInAliasOrAliasSupportSentences =
        ObjectSentenceAliasSentence SentenceAlias
            { sentenceAliasAlias = Alias
                { aliasConstructor = Id "alias2"
                , aliasParams = [SortVariable (Id "sv1")]
                }
            , sentenceAliasSorts =
                [ SortVariableSort (SortVariable (Id "sv1")) ]
            , sentenceAliasResultSort =
                SortVariableSort (SortVariable (Id "sv1"))
            , sentenceAliasAttributes = Attributes []
            }
        : defaultAliasSupportSentences


defaultSort :: Sort Object
defaultSort = SortActualSort SortActual
    { sortActualName = Id "sort1"
    , sortActualSorts = []
    }
defaultSortDeclaration :: Sentence
defaultSortDeclaration = SentenceSortSentence SentenceSort
    { sentenceSortName = Id "sort1"
    , sentenceSortParameters = []
    , sentenceSortAttributes = Attributes []
    }

newtype DeclaringSentence = DeclaringSentence Sentence
newtype UsingSentence = UsingSentence Sentence
newtype SupportingSentences = SupportingSentences [Sentence]

nameReferenceTests
    :: String
    -> ExpectedErrorMessage
    -> ErrorStack
    -> DeclaringSentence
    -> UsingSentence
    -> SupportingSentences
    -> TestTree
nameReferenceTests
    description
    expectedErrorMessage
    additionalErrorStack
    declaringSentence
    usingSentence
    supportingSentences
  =
    testGroup description
        (  nameReferenceSuccessTests
            declaringSentence usingSentence supportingSentences
        ++ nameReferenceFailureTests
            expectedErrorMessage additionalErrorStack
            declaringSentence usingSentence supportingSentences
        )

nameReferenceSuccessTests
    :: DeclaringSentence
    -> UsingSentence
    -> SupportingSentences
    -> [TestTree]
nameReferenceSuccessTests
    (DeclaringSentence declaringSentence)
    (UsingSentence usingSentence)
    (SupportingSentences supportingSentences)
  =
    [ expectSuccess "Successful reference: one module"
        Definition
            { definitionAttributes = Attributes []
            , definitionModules =
                [ Module
                    { moduleName = ModuleName "M1"
                    , moduleSentences =
                        usingSentence
                        : declaringSentence
                        : supportingSentences
                    , moduleAttributes = Attributes []
                    }
                ]
            }
    , expectSuccess "Successful reference: two modules with import"
        Definition
            { definitionAttributes = Attributes []
            , definitionModules =
                [ Module
                    { moduleName = ModuleName "M1"
                    , moduleSentences =
                        [ importSentence (ModuleName "M2"), usingSentence]
                    , moduleAttributes = Attributes []
                    }
                , Module
                    { moduleName = ModuleName "M2"
                    , moduleSentences =
                        declaringSentence : supportingSentences
                    , moduleAttributes = Attributes []
                    }
                ]
            }
    , expectSuccess "Successful reference: three modules with chain import"
        Definition
            { definitionAttributes = Attributes []
            , definitionModules =
                [ Module
                    { moduleName = ModuleName "M1"
                    , moduleSentences =
                        [ importSentence (ModuleName "M2"), usingSentence]
                    , moduleAttributes = Attributes []
                    }
                , Module
                    { moduleName = ModuleName "M2"
                    , moduleSentences = [ importSentence (ModuleName "M3") ]
                    , moduleAttributes = Attributes []
                    }
                , Module
                    { moduleName = ModuleName "M3"
                    , moduleSentences =
                        declaringSentence : supportingSentences
                    , moduleAttributes = Attributes []
                    }
                ]
            }
    , expectSuccess "Successful reference: three modules with tree import"
        Definition
            { definitionAttributes = Attributes []
            , definitionModules =
                [ Module
                    { moduleName = ModuleName "M1"
                    , moduleSentences =
                        [ importSentence (ModuleName "M2")
                        , importSentence (ModuleName "M3")
                        , usingSentence
                        ]
                    , moduleAttributes = Attributes []
                    }
                , Module
                    { moduleName = ModuleName "M2"
                    , moduleSentences = []
                    , moduleAttributes = Attributes []
                    }
                , Module
                    { moduleName = ModuleName "M3"
                    , moduleSentences =
                        declaringSentence : supportingSentences
                    , moduleAttributes = Attributes []
                    }
                ]
            }
    , expectSuccess "Successful reference: three modules with dag import"
        Definition
            { definitionAttributes = Attributes []
            , definitionModules =
                [ Module
                    { moduleName = ModuleName "M1"
                    , moduleSentences =
                        [ importSentence (ModuleName "M2")
                        , importSentence (ModuleName "M3")
                        , usingSentence
                        ]
                    , moduleAttributes = Attributes []
                    }
                , Module
                    { moduleName = ModuleName "M2"
                    , moduleSentences = [ importSentence (ModuleName "M3") ]
                    , moduleAttributes = Attributes []
                    }
                , Module
                    { moduleName = ModuleName "M3"
                    , moduleSentences =
                        declaringSentence : supportingSentences
                    , moduleAttributes = Attributes []
                    }
                ]
            }
    ]

nameReferenceFailureTests
    :: ExpectedErrorMessage
    -> ErrorStack
    -> DeclaringSentence
    -> UsingSentence
    -> SupportingSentences
    -> [TestTree]
nameReferenceFailureTests
    (ExpectedErrorMessage expectedErrorMessage)
    (ErrorStack additionalErrorStack)
    (DeclaringSentence declaringSentence)
    (UsingSentence usingSentence)
    (SupportingSentences supportingSentences)
  =
    [ expectFailureWithError
        "Failed reference: One module without declaration"
        Error
            { errorContext = "module 'M1'" : additionalErrorStack
            , errorError = expectedErrorMessage
            }
        Definition
            { definitionAttributes = Attributes []
            , definitionModules =
                [ Module
                    { moduleName = ModuleName "M1"
                    , moduleSentences = usingSentence : supportingSentences
                    , moduleAttributes = Attributes []
                    }
                ]
            }
    , expectFailureWithError
        "Failed reference: two modules without import"
        Error
            { errorContext = "module 'M1'" : additionalErrorStack
            , errorError = expectedErrorMessage
            }
        Definition
            { definitionAttributes = Attributes []
            , definitionModules =
                [ Module
                    { moduleName = ModuleName "M1"
                    , moduleSentences = usingSentence : supportingSentences
                    , moduleAttributes = Attributes []
                    }
                , Module
                    { moduleName = ModuleName "M2"
                    , moduleSentences = [ declaringSentence ]
                    , moduleAttributes = Attributes []
                    }
                ]
            }
    , expectFailureWithError
        "Failed reference: two modules with reverse import"
        Error
            { errorContext = "module 'M2'" : additionalErrorStack
            , errorError = expectedErrorMessage
            }
        Definition
            { definitionAttributes = Attributes []
            , definitionModules =
                [ Module
                    { moduleName = ModuleName "M1"
                    , moduleSentences =
                        [ importSentence (ModuleName "M2")
                        , declaringSentence
                        ]
                    , moduleAttributes = Attributes []
                    }
                , Module
                    { moduleName = ModuleName "M2"
                    , moduleSentences = usingSentence : supportingSentences
                    , moduleAttributes = Attributes []
                    }
                ]
            }
    ]

nameDuplicationTests :: TestTree
nameDuplicationTests =
    testGroup
        "Name duplication accross modules"
        [ duplicatedNameFailureTest
            "Two sorts with the same name"
            "s1"
            (sortDeclarationModule (ModuleName "M1") (SortName "s1"))
            (sortDeclarationModule (ModuleName "M2") (SortName "s1"))
        , duplicatedNameFailureTest
            "Sort with the same name as symbol"
            "name"
            (sortDeclarationModule (ModuleName "M1") (SortName "name"))
            (symbolDeclarationModule (ModuleName "M2") (SymbolName "name"))
        , duplicatedNameFailureTest
            "Sort with the same name as symbol"
            "name"
            (symbolDeclarationModule (ModuleName "M1") (SymbolName "name"))
            (sortDeclarationModule (ModuleName "M2") (SortName "name"))
        , duplicatedNameFailureTest
            "Sort with the same name as alias"
            "name"
            (sortDeclarationModule (ModuleName "M1") (SortName "name"))
            (aliasDeclarationModule (ModuleName "M2") (AliasName "name"))
        , duplicatedNameFailureTest
            "Sort with the same name as alias"
            "name"
            (aliasDeclarationModule (ModuleName "M1") (AliasName "name"))
            (sortDeclarationModule (ModuleName "M2") (SortName "name"))

        , duplicatedNameFailureTest
            "Two symbols with the same name"
            "name"
            (symbolDeclarationModule (ModuleName "M1") (SymbolName "name"))
            (symbolDeclarationModule (ModuleName "M2") (SymbolName "name"))
        , duplicatedNameFailureTest
            "Symbol with the same name as alias"
            "name"
            (aliasDeclarationModule (ModuleName "M1") (AliasName "name"))
            (aliasDeclarationModule (ModuleName "M2") (AliasName "name"))
        , duplicatedNameFailureTest
            "Symbol with the same name as alias"
            "name"
            (aliasDeclarationModule (ModuleName "M1") (AliasName "name"))
            (symbolDeclarationModule (ModuleName "M2") (SymbolName "name"))

        , duplicatedNameFailureTest
            "Two aliases with the same name"
            "name"
            (aliasDeclarationModule (ModuleName "M1") (AliasName "name"))
            (aliasDeclarationModule (ModuleName "M2") (AliasName "name"))
        ]
  where
    sortDeclarationModule modName (SortName sortName) =
        Module
            { moduleName = modName
            , moduleSentences =
                [ SentenceSortSentence SentenceSort
                    { sentenceSortName = Id sortName
                    , sentenceSortParameters = []
                    , sentenceSortAttributes = Attributes []
                    }
                ]
            , moduleAttributes = Attributes []
            }
    symbolDeclarationModule modName (SymbolName symbolName) =
        Module
            { moduleName = modName
            , moduleSentences =
                [ ObjectSentenceSymbolSentence SentenceSymbol
                    { sentenceSymbolSymbol = Symbol
                        { symbolConstructor = Id symbolName
                        , symbolParams = [SortVariable (Id "sv1")]
                        }
                    , sentenceSymbolSorts = []
                    , sentenceSymbolResultSort =
                        SortVariableSort (SortVariable (Id "sv1"))
                    , sentenceSymbolAttributes = Attributes []
                    }
                ]
            , moduleAttributes = Attributes []
            }
    aliasDeclarationModule modName (AliasName aliasName) =
        Module
            { moduleName = modName
            , moduleSentences =
                [ ObjectSentenceAliasSentence SentenceAlias
                    { sentenceAliasAlias = Alias
                        { aliasConstructor = Id aliasName
                        , aliasParams = [SortVariable (Id "sv1")]
                        }
                    , sentenceAliasSorts = []
                    , sentenceAliasResultSort =
                        SortVariableSort (SortVariable (Id "sv1"))
                    , sentenceAliasAttributes = Attributes []
                    }
                ]
            , moduleAttributes = Attributes []
            }

duplicatedNameFailureTest
    :: String -> String -> Module -> Module -> TestTree
duplicatedNameFailureTest message duplicatedName module1 module2 =
    expectFailureWithError
        message
        Error
            { errorContext = ["module 'M2'"]
            , errorError = "Duplicated name: '" ++ duplicatedName ++ "'."
            }
        Definition
            { definitionAttributes = Attributes []
            , definitionModules =
                [ module1
                , module2
                ]
            }
