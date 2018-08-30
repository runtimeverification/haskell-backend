module Test.Kore.ASTVerifier.DefinitionVerifier.Imports
    ( test_imports
    ) where

import Test.Tasty
       ( TestTree, testGroup )

import Kore.AST.Common
import Kore.AST.Kore
import Kore.AST.MetaOrObject
import Kore.AST.Sentence
import Kore.Error
import Kore.Implicit.ImplicitSorts

import Test.Kore
import Test.Kore.ASTVerifier.DefinitionVerifier

test_imports :: [TestTree]
test_imports =
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
            , "\\top (<test data>)"
            , "sort 'sort2' (<test data>)"
            , "sort 'sort1' (<test data>)"
            , "(<test data>)"
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
            , "\\top (<test data>)"
            , "sort 'sort1' (<test data>)"
            , "(<test data>)"
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
            , "\\exists 'var' (<test data>)"
            , "sort 'sort1' (<test data>)"
            , "(<test data>)"
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
            , "\\and (<test data>)"
            , "sort 'sort1' (<test data>)"
            , "(<test data>)"
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
            , "\\next (<test data>)"
            , "sort 'sort1' (<test data>)"
            , "(<test data>)"
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
            , "\\next (<test data>)"
            , "\\equals (<test data>)"
            , "sort 'sort1' (<test data>)"
            , "(<test data>)"
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
            [ "symbol 'symbol1' declaration (<test data>)"
            , "sort 'sort1' (<test data>)"
            , "(<test data>)"
            ]
        )
        (DeclaringSentence sortDeclaration)
        (UsingSentence sortReferenceInSentenceSymbolResultSortSentence)
        (SupportingSentences [])
    , nameReferenceTests
        "Sort visibility in symbol declaration - operand sort"
        (ExpectedErrorMessage "Sort 'sort1' not declared.")
        (ErrorStack
            [ "symbol 'symbol1' declaration (<test data>)"
            , "sort 'sort1' (<test data>)"
            , "(<test data>)"
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
            [ "alias 'alias1' declaration (<test data>)"
            , "sort 'sort1' (<test data>)"
            , "(<test data>)"
            ]
        )
        (DeclaringSentence sortDeclaration)
        (UsingSentence sortReferenceInSentenceAliasResultSortSentence)
        (SupportingSentences [])
    , nameReferenceTests
        "Sort visibility in alias declaration - operand sort"
        (ExpectedErrorMessage "Sort 'sort1' not declared.")
        (ErrorStack
            [ "alias 'alias1' declaration (<test data>)"
            , "sort 'sort1' (<test data>)"
            , "(<test data>)"
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
            , "symbol or alias 'symbol2' (<test data>)"
            , "sort 'sort1' (<test data>)"
            , "(<test data>)"
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
        { sortActualName = testId "sort1"
        , sortActualSorts = []
        } :: Sort Object
    sortDeclaration = asSentence
        (SentenceSort
            { sentenceSortName = testId "sort1"
            , sentenceSortParameters = []
            , sentenceSortAttributes = Attributes []
            }
        ::KoreSentenceSort Object)
    anotherSort = SortActualSort SortActual
        { sortActualName = testId "sort3"
        , sortActualSorts = []
        } :: Sort Object
    anotherSortDeclaration = asSentence
        (SentenceSort
            { sentenceSortName = testId "sort3"
            , sentenceSortParameters = []
            , sentenceSortAttributes = Attributes []
            }
        :: KoreSentenceSort Object)
    topSortPattern = asKorePattern ( TopPattern Top { topSort = sort } )
    metaTopSortPattern =
        asKorePattern ( TopPattern Top { topSort = charMetaSort } )
    sortReferenceInSort =
        SortActualSort SortActual
            { sortActualName = testId "sort2"
            , sortActualSorts = [ sort ]
            } :: Sort Object
    sortReferenceInSortSentence =
        asSentence
            (SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = asKorePattern
                    ( TopPattern Top { topSort = sortReferenceInSort } )
                , sentenceAxiomAttributes = Attributes []
                }
            :: KoreSentenceAxiom)
    sortReferenceInSortSupportingSentences =
        [ asSentence
            (SentenceSort
                { sentenceSortName = testId "sort2"
                , sentenceSortParameters = [SortVariable (testId "x")]
                , sentenceSortAttributes = Attributes []
                }
            :: KoreSentenceSort Object)
        ]
    sortReferenceInTopPatternSentence =
        asSentence
            (SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = topSortPattern
                , sentenceAxiomAttributes = Attributes []
                }
            :: KoreSentenceAxiom)
    metaSortReferenceInTopPatternSentence =
        asSentence
            (SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = metaTopSortPattern
                , sentenceAxiomAttributes = Attributes []
                }
            :: KoreSentenceAxiom)
    sortReferenceInExistsPatternSentence =
        asSentence
            (SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = asKorePattern
                    ( ExistsPattern Exists
                        { existsSort = sort
                        , existsVariable = Variable
                            { variableName = testId "var"
                            , variableSort = sort
                            }
                        , existsChild = asKorePattern
                            ( VariablePattern Variable
                                { variableName = testId "var"
                                , variableSort = sort
                                }
                            )
                        }
                    )
                , sentenceAxiomAttributes = Attributes []
                }
            :: KoreSentenceAxiom)
    sortReferenceInAndPatternSentence =
        asSentence
            (SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = asKorePattern
                    ( AndPattern And
                        { andSort = sort
                        , andFirst = topSortPattern
                        , andSecond = topSortPattern
                        }
                    )
                , sentenceAxiomAttributes = Attributes []
                }
            :: KoreSentenceAxiom)
    sortReferenceInNextPatternSentence =
        asSentence
            (SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = asKorePattern
                    ( NextPattern Next
                        { nextSort = sort
                        , nextChild = topSortPattern
                        }
                    )
                , sentenceAxiomAttributes = Attributes []
                }
            :: KoreSentenceAxiom)
    sortReferenceInPatternInPatternSentence =
        asSentence
            (SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = asKorePattern
                    ( NextPattern Next
                        { nextSort = anotherSort
                        , nextChild = asKorePattern
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
            :: KoreSentenceAxiom)
    sortReferenceInPatternInPatternSupportingSentences =
        [ anotherSortDeclaration ]
    sortReferenceInSentenceSymbolResultSortSentence =
        asSentence
            (SentenceSymbol
                { sentenceSymbolSymbol = Symbol
                    { symbolConstructor = testId "symbol1"
                    , symbolParams = []
                    }
                , sentenceSymbolSorts = []
                , sentenceSymbolResultSort = sort
                , sentenceSymbolAttributes = Attributes []
                }
            :: KoreSentenceSymbol Object)
    sortReferenceInSentenceSymbolSortsSentence =
        asSentence
            (SentenceSymbol
                { sentenceSymbolSymbol = Symbol
                    { symbolConstructor = testId "symbol1"
                    , symbolParams = []
                    }
                , sentenceSymbolSorts = [sort]
                , sentenceSymbolResultSort = anotherSort
                , sentenceSymbolAttributes = Attributes []
                }
            :: KoreSentenceSymbol Object)
    sortReferenceInSentenceSymbolSortsSupportSentences =
        [ anotherSortDeclaration ]
    sortReferenceInSentenceAliasResultSortSentence =
        asSentence
            (SentenceAlias
                { sentenceAliasAlias = Alias
                    { aliasConstructor = testId "alias1"
                    , aliasParams = []
                    }
                , sentenceAliasSorts = []
                , sentenceAliasResultSort = sort
                , sentenceAliasLeftPattern  = TopPattern $ Top { topSort = sort }
                , sentenceAliasRightPattern = TopPattern $ Top { topSort = sort }
                , sentenceAliasAttributes = Attributes []
                }
            :: KoreSentenceAlias Object)
    sortReferenceInSentenceAliasSortsSentence =
        asSentence
            (SentenceAlias
                { sentenceAliasAlias = Alias
                    { aliasConstructor = testId "alias1"
                    , aliasParams = []
                    }
                , sentenceAliasSorts = [sort]
                , sentenceAliasResultSort = anotherSort
                , sentenceAliasLeftPattern  = TopPattern $ Top { topSort = sort }
                , sentenceAliasRightPattern = TopPattern $ Top { topSort = sort }
                , sentenceAliasAttributes = Attributes []
                }
            :: KoreSentenceAlias Object)
    sortReferenceInSentenceAliasSortsSupportSentences =
        [ anotherSortDeclaration ]
    sortReferenceInSymbolOrAliasSentence =
        asSentence
            (SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = asKorePattern
                    ( ApplicationPattern Application
                        { applicationSymbolOrAlias = SymbolOrAlias
                            { symbolOrAliasConstructor = testId "symbol2"
                            , symbolOrAliasParams = [ sort ]
                            }
                        , applicationChildren = []
                        }
                    )
                , sentenceAxiomAttributes = Attributes []
                }
            :: KoreSentenceAxiom)
    sortReferenceInSymbolOrAliasSupportSentences =
        [ asSentence
            (SentenceSymbol
                { sentenceSymbolSymbol = Symbol
                    { symbolConstructor = testId "symbol2"
                    , symbolParams = [SortVariable (testId "sv1")]
                    }
                , sentenceSymbolSorts = []
                , sentenceSymbolResultSort =
                    SortVariableSort (SortVariable (testId "sv1"))
                , sentenceSymbolAttributes = Attributes []
                }
            :: KoreSentenceSymbol Object)
        ]

symbolVisibilityTests :: [TestTree]
symbolVisibilityTests =
    [ nameReferenceTests
        "Symbol visibility in axioms"
        (ExpectedErrorMessage "Symbol 'symbol1' not defined.")
        (ErrorStack
            [ "axiom declaration"
            , "symbol or alias 'symbol1' (<test data>)"
            , "(<test data>)"
            ]
        )
        (DeclaringSentence symbolDeclaration)
        (UsingSentence symbolReferenceInAxiomSentence)
        (SupportingSentences defaultSymbolSupportSentences)
    , nameReferenceTests
        "Symbol visibility in and pattern"
        (ExpectedErrorMessage "Symbol 'symbol1' not defined.")
        (ErrorStack
            [ "axiom declaration"
            , "\\and (<test data>)"
            , "symbol or alias 'symbol1' (<test data>)"
            , "(<test data>)"
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
            , "\\exists 'var' (<test data>)"
            , "symbol or alias 'symbol1' (<test data>)"
            , "(<test data>)"
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
            , "\\next (<test data>)"
            , "symbol or alias 'symbol1' (<test data>)"
            , "(<test data>)"
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
            , "symbol or alias 'symbol2' (<test data>)"
            , "symbol or alias 'symbol1' (<test data>)"
            , "(<test data>)"
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
            , "symbol or alias '#symbol1' (<test data>)"
            , "(<test data>)"
            ]
        )
        (DeclaringSentence metaSymbolDeclaration)
        (UsingSentence metaSymbolReferenceInAxiomSentence)
        (SupportingSentences [])
    ]
  where
    topSortPattern = asKorePattern ( TopPattern Top { topSort = defaultSort } )
    symbolPattern :: CommonKorePattern
    symbolPattern = asKorePattern
        ( ApplicationPattern Application
            { applicationSymbolOrAlias = SymbolOrAlias
                { symbolOrAliasConstructor = testId "symbol1"
                , symbolOrAliasParams = [ defaultSort ]
                }
            , applicationChildren = []
            }
        )
    symbolDeclaration = asSentence
        (SentenceSymbol
            { sentenceSymbolSymbol = Symbol
                { symbolConstructor = testId "symbol1"
                , symbolParams = [SortVariable (testId "sv1")]
                }
            , sentenceSymbolSorts = []
            , sentenceSymbolResultSort =
                SortVariableSort (SortVariable (testId "sv1"))
            , sentenceSymbolAttributes = Attributes []
            }
        :: KoreSentenceSymbol Object)
    defaultSymbolSupportSentences = [ defaultSortDeclaration ]
    metaSymbolPattern = asKorePattern
        ( ApplicationPattern Application
            { applicationSymbolOrAlias = SymbolOrAlias
                { symbolOrAliasConstructor = testId "#symbol1"
                , symbolOrAliasParams = [ charMetaSort ]
                }
            , applicationChildren = []
            }
        )
    metaSymbolDeclaration = asSentence
        (SentenceSymbol
            { sentenceSymbolSymbol = Symbol
                { symbolConstructor = testId "#symbol1"
                , symbolParams = [SortVariable (testId "#sv1")]
                }
            , sentenceSymbolSorts = []
            , sentenceSymbolResultSort =
                SortVariableSort (SortVariable (testId "#sv1"))
            , sentenceSymbolAttributes = Attributes []
            }
        :: KoreSentenceSymbol Meta)
    symbolReferenceInAxiomSentence =
        asSentence
            (SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = symbolPattern
                , sentenceAxiomAttributes = Attributes []
                }
            :: KoreSentenceAxiom)
    metaSymbolReferenceInAxiomSentence =
        asSentence
            (SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = metaSymbolPattern
                , sentenceAxiomAttributes = Attributes []
                }
            :: KoreSentenceAxiom)
    symbolReferenceInAndPatternSentence =
        asSentence
            (SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = asKorePattern
                    ( AndPattern And
                        { andSort = defaultSort
                        , andFirst = symbolPattern
                        , andSecond = topSortPattern
                        }
                    )
                , sentenceAxiomAttributes = Attributes []
                }
            :: KoreSentenceAxiom)
    symbolReferenceInExistsPatternSentence =
        asSentence
            (SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = asKorePattern
                    ( ExistsPattern Exists
                        { existsSort = defaultSort
                        , existsVariable = Variable
                            { variableName = testId "var"
                            , variableSort = defaultSort
                            }
                        , existsChild = symbolPattern
                        }
                    )
                , sentenceAxiomAttributes = Attributes []
                }
            :: KoreSentenceAxiom)
    symbolReferenceInNextPatternSentence =
        asSentence
            (SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = asKorePattern
                    ( NextPattern Next
                        { nextSort = defaultSort
                        , nextChild = symbolPattern
                        }
                    )
                , sentenceAxiomAttributes = Attributes []
                }
            :: KoreSentenceAxiom)
    symbolReferenceInSymbolOrAliasSentence =
        asSentence
            (SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = asKorePattern
                    ( ApplicationPattern Application
                        { applicationSymbolOrAlias = SymbolOrAlias
                            { symbolOrAliasConstructor = testId "symbol2"
                            , symbolOrAliasParams = [ defaultSort ]
                            }
                        , applicationChildren = [symbolPattern]
                        }
                    )
                , sentenceAxiomAttributes = Attributes []
                }
            :: KoreSentenceAxiom)
    symbolReferenceInSymbolOrAliasSupportSentences =
        asSentence
            (SentenceSymbol
                { sentenceSymbolSymbol = Symbol
                    { symbolConstructor = testId "symbol2"
                    , symbolParams = [SortVariable (testId "sv1")]
                    }
                , sentenceSymbolSorts =
                    [ SortVariableSort (SortVariable (testId "sv1")) ]
                , sentenceSymbolResultSort =
                    SortVariableSort (SortVariable (testId "sv1"))
                , sentenceSymbolAttributes = Attributes []
                }
            :: KoreSentenceSymbol Object)
        : defaultSymbolSupportSentences

aliasVisibilityTests :: [TestTree]
aliasVisibilityTests =
    [ nameReferenceTests
        "Alias visibility in axioms"
        (ExpectedErrorMessage "Symbol 'alias1' not defined.")
        (ErrorStack
            [ "axiom declaration"
            , "symbol or alias 'alias1' (<test data>)"
            , "(<test data>)"
            ]
        )
        (DeclaringSentence aliasDeclaration)
        (UsingSentence aliasReferenceInAxiomSentence)
        (SupportingSentences defaultAliasSupportSentences)
    , nameReferenceTests
        "Alias visibility in and pattern"
        (ExpectedErrorMessage "Symbol 'alias1' not defined.")
        (ErrorStack
            [ "axiom declaration"
            , "\\and (<test data>)"
            , "symbol or alias 'alias1' (<test data>)"
            , "(<test data>)"
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
            , "\\exists 'var' (<test data>)"
            , "symbol or alias 'alias1' (<test data>)"
            , "(<test data>)"
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
            , "\\next (<test data>)"
            , "symbol or alias 'alias1' (<test data>)"
            , "(<test data>)"
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
            , "symbol or alias 'alias2' (<test data>)"
            , "symbol or alias 'alias1' (<test data>)"
            , "(<test data>)"
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
            , "symbol or alias '#alias1' (<test data>)"
            , "(<test data>)"
            ]
        )
        (DeclaringSentence metaAliasDeclaration)
        (UsingSentence metaAliasReferenceInAxiomSentence)
        (SupportingSentences [])
    ]
  where
    topSortPattern = asKorePattern ( TopPattern Top { topSort = defaultSort } )
    aliasPattern :: CommonKorePattern
    aliasPattern = asKorePattern
        ( ApplicationPattern Application
            { applicationSymbolOrAlias = SymbolOrAlias
                { symbolOrAliasConstructor = testId "alias1"
                , symbolOrAliasParams = [ defaultSort ]
                }
            , applicationChildren = []
            }
        )
    aliasDeclaration = asSentence
        (SentenceAlias
            { sentenceAliasAlias = Alias
                { aliasConstructor = testId "alias1"
                , aliasParams = [SortVariable (testId "sv1")]
                }
            , sentenceAliasSorts = []
            , sentenceAliasResultSort =
                SortVariableSort (SortVariable (testId "sv1"))
            , sentenceAliasLeftPattern  = TopPattern $ Top { topSort = defaultSort }
            , sentenceAliasRightPattern = TopPattern $ Top { topSort = defaultSort }
            , sentenceAliasAttributes = Attributes []
            }
        :: KoreSentenceAlias Object)
    defaultAliasSupportSentences = [ defaultSortDeclaration ]
    metaAliasPattern = asKorePattern
        ( ApplicationPattern Application
            { applicationSymbolOrAlias = SymbolOrAlias
                { symbolOrAliasConstructor = testId "#alias1"
                , symbolOrAliasParams = [ charMetaSort ]
                }
            , applicationChildren = []
            }
        )
    metaAliasDeclaration = asSentence
        (SentenceAlias
            { sentenceAliasAlias = Alias
                { aliasConstructor = testId "#alias1"
                , aliasParams = [SortVariable (testId "#sv1")]
                }
            , sentenceAliasSorts = []
            , sentenceAliasResultSort =
                SortVariableSort (SortVariable (testId "#sv1"))
            , sentenceAliasLeftPattern  = TopPattern $ Top { topSort = patternMetaSort }
            , sentenceAliasRightPattern = TopPattern $ Top { topSort = patternMetaSort }
            , sentenceAliasAttributes = Attributes []
            }
        :: KoreSentenceAlias Meta)
    aliasReferenceInAxiomSentence =
        asSentence
            (SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = aliasPattern
                , sentenceAxiomAttributes = Attributes []
                }
            :: KoreSentenceAxiom)
    metaAliasReferenceInAxiomSentence =
        asSentence
            (SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = metaAliasPattern
                , sentenceAxiomAttributes = Attributes []
                }
            :: KoreSentenceAxiom)
    aliasReferenceInAndPatternSentence =
        asSentence
            (SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = asKorePattern
                    ( AndPattern And
                        { andSort = defaultSort
                        , andFirst = aliasPattern
                        , andSecond = topSortPattern
                        }
                    )
                , sentenceAxiomAttributes = Attributes []
                }
            :: KoreSentenceAxiom)
    aliasReferenceInExistsPatternSentence =
        asSentence
            (SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = asKorePattern
                    ( ExistsPattern Exists
                        { existsSort = defaultSort
                        , existsVariable = Variable
                            { variableName = testId "var"
                            , variableSort = defaultSort
                            }
                        , existsChild = aliasPattern
                        }
                    )
                , sentenceAxiomAttributes = Attributes []
                }
            :: KoreSentenceAxiom)
    aliasReferenceInNextPatternSentence =
        asSentence
            (SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = asKorePattern
                    ( NextPattern Next
                        { nextSort = defaultSort
                        , nextChild = aliasPattern
                        }
                    )
                , sentenceAxiomAttributes = Attributes []
                }
            :: KoreSentenceAxiom)
    aliasReferenceInAliasOrAliasSentence =
        asSentence
            (SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = asKorePattern
                    ( ApplicationPattern Application
                        { applicationSymbolOrAlias = SymbolOrAlias
                            { symbolOrAliasConstructor = testId "alias2"
                            , symbolOrAliasParams = [ defaultSort ]
                            }
                        , applicationChildren = [aliasPattern]
                        }
                    )
                , sentenceAxiomAttributes = Attributes []
                }
            :: KoreSentenceAxiom)
    aliasReferenceInAliasOrAliasSupportSentences =
        asSentence
            (SentenceAlias
                { sentenceAliasAlias = Alias
                    { aliasConstructor = testId "alias2"
                    , aliasParams = [SortVariable (testId "sv1")]
                    }
                , sentenceAliasSorts =
                    [ SortVariableSort (SortVariable (testId "sv1")) ]
                , sentenceAliasResultSort =
                    SortVariableSort (SortVariable (testId "sv1"))
                , sentenceAliasLeftPattern  = TopPattern $ Top { topSort = defaultSort }
                , sentenceAliasRightPattern = TopPattern $ Top { topSort = defaultSort }
                , sentenceAliasAttributes = Attributes []
                }
            :: KoreSentenceAlias Object)
        : defaultAliasSupportSentences


defaultSort :: Sort Object
defaultSort = SortActualSort SortActual
    { sortActualName = testId "sort1"
    , sortActualSorts = []
    }
defaultSortDeclaration :: KoreSentence
defaultSortDeclaration = asSentence
    (SentenceSort
        { sentenceSortName = testId "sort1"
        , sentenceSortParameters = []
        , sentenceSortAttributes = Attributes []
        }
    :: KoreSentenceSort Object)

newtype DeclaringSentence = DeclaringSentence KoreSentence
newtype UsingSentence = UsingSentence KoreSentence
newtype SupportingSentences = SupportingSentences [KoreSentence]

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
                [ asSentence
                    (SentenceSort
                        { sentenceSortName = testId sortName
                        , sentenceSortParameters = []
                        , sentenceSortAttributes = Attributes []
                        }
                    :: KoreSentenceSort Object)
                ]
            , moduleAttributes = Attributes []
            }
    symbolDeclarationModule modName (SymbolName symbolName) =
        Module
            { moduleName = modName
            , moduleSentences =
                [ asSentence
                    (SentenceSymbol
                        { sentenceSymbolSymbol = Symbol
                            { symbolConstructor = testId symbolName
                            , symbolParams = [SortVariable (testId "sv1")]
                            }
                        , sentenceSymbolSorts = []
                        , sentenceSymbolResultSort =
                            SortVariableSort (SortVariable (testId "sv1"))
                        , sentenceSymbolAttributes = Attributes []
                        }
                    :: KoreSentenceSymbol Object)
                ]
            , moduleAttributes = Attributes []
            }
    aliasDeclarationModule modName (AliasName aliasName) =
        Module
            { moduleName = modName
            , moduleSentences =
                [ asSentence
                    (SentenceAlias
                        { sentenceAliasAlias = Alias
                            { aliasConstructor = testId aliasName
                            , aliasParams = [SortVariable (testId "sv1")]
                            }
                        , sentenceAliasSorts = []
                        , sentenceAliasResultSort =
                            SortVariableSort (SortVariable (testId "sv1"))
                        , sentenceAliasLeftPattern = TopPattern $ Top { topSort = simpleSort (SortName "s1") }
                        , sentenceAliasRightPattern = TopPattern $ Top { topSort = simpleSort (SortName "s1") }
                        , sentenceAliasAttributes = Attributes []
                        }
                    :: KoreSentenceAlias Object)
                ]
            , moduleAttributes = Attributes []
            }

duplicatedNameFailureTest
    :: String -> String -> KoreModule -> KoreModule -> TestTree
duplicatedNameFailureTest message duplicatedName module1 module2 =
    expectFailureWithError
        message
        Error
            { errorContext = ["module 'M2'", "(<test data>, <test data>)"]
            , errorError = "Duplicated name: '" ++ duplicatedName ++ "'."
            }
        Definition
            { definitionAttributes = Attributes []
            , definitionModules =
                [ module1
                , module2
                ]
            }
