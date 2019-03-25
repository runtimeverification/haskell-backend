module Test.Kore.ASTVerifier.DefinitionVerifier.Imports
    ( test_imports
    ) where

import Test.Tasty
       ( TestTree, testGroup )

import GHC.Stack
       ( HasCallStack )

import Kore.AST.Kore
import Kore.AST.Sentence
import Kore.AST.Valid
import Kore.Error
import Kore.Implicit.ImplicitSorts
import Kore.Step.Pattern

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
        :: VerifiedKoreSentenceSort Object)
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
        :: VerifiedKoreSentenceSort Object)
    topSortPattern = toKorePattern $ mkTop sort
    metaTopSortPattern = toKorePattern $ mkTop charMetaSort
    sortReferenceInSort =
        SortActualSort SortActual
            { sortActualName = testId "sort2"
            , sortActualSorts = [ sort ]
            } :: Sort Object
    sortReferenceInSortSentence =
        asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    toKorePattern $ mkTop sortReferenceInSort
                , sentenceAxiomAttributes = Attributes []
                }
    sortReferenceInSortSupportingSentences =
        [ asSentence
            (SentenceSort
                { sentenceSortName = testId "sort2"
                , sentenceSortParameters = [SortVariable (testId "x")]
                , sentenceSortAttributes = Attributes []
                }
            :: VerifiedKoreSentenceSort Object)
        ]
    sortReferenceInTopPatternSentence =
        asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = topSortPattern
                , sentenceAxiomAttributes = Attributes []
                }
    metaSortReferenceInTopPatternSentence =
        asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = metaTopSortPattern
                , sentenceAxiomAttributes = Attributes []
                }
    sortReferenceInExistsPatternSentence =
        asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    toKorePattern
                        (mkExists existsVariable (mkVar existsVariable))
                , sentenceAxiomAttributes = Attributes []
                }
      where
        existsVariable =
            Variable
                { variableName = testId "var"
                , variableCounter = mempty
                , variableSort = sort
                }
    sortReferenceInAndPatternSentence =
        asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    toKorePattern $ mkAnd (mkTop sort) mkTop_
                , sentenceAxiomAttributes = Attributes []
                }
    sortReferenceInNextPatternSentence =
        asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    toKorePattern
                        (mkNext (mkTop sort))
                , sentenceAxiomAttributes = Attributes []
                }
    sortReferenceInPatternInPatternSentence =
        asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    toKorePattern
                        (mkNext
                            (mkEquals
                                anotherSort
                                (mkTop sort)
                                (mkTop sort)
                            )
                        )
                , sentenceAxiomAttributes = Attributes []
                }
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
            :: VerifiedKoreSentenceSymbol Object)
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
            :: VerifiedKoreSentenceSymbol Object)
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
                , sentenceAliasLeftPattern =
                    Application
                        { applicationSymbolOrAlias =
                            SymbolOrAlias
                                { symbolOrAliasConstructor = testId "alias1"
                                , symbolOrAliasParams = []
                                }
                        , applicationChildren = []
                        }
                , sentenceAliasRightPattern =
                    toKorePattern $ mkTop sort
                , sentenceAliasAttributes = Attributes []
                }
            :: VerifiedKoreSentenceAlias Object)
    sortReferenceInSentenceAliasSortsSentence =
        asSentence
            (SentenceAlias
                { sentenceAliasAlias = Alias
                    { aliasConstructor = testId "alias1"
                    , aliasParams = []
                    }
                , sentenceAliasSorts = [sort]
                , sentenceAliasResultSort = anotherSort
                , sentenceAliasLeftPattern =
                    Application
                        { applicationSymbolOrAlias =
                            SymbolOrAlias
                                { symbolOrAliasConstructor = testId "alias1"
                                , symbolOrAliasParams = []
                                }
                        , applicationChildren =
                            [ Variable
                                { variableSort = sort
                                , variableCounter = mempty
                                , variableName = testId "x"
                                }
                            ]
                        }
                , sentenceAliasRightPattern =
                    toKorePattern $ mkTop anotherSort
                , sentenceAliasAttributes = Attributes []
                }
            :: VerifiedKoreSentenceAlias Object)
    sortReferenceInSentenceAliasSortsSupportSentences =
        [ anotherSortDeclaration ]
    sortReferenceInSymbolOrAliasSentence =
        asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    toKorePattern
                        (mkApp
                            sort
                            SymbolOrAlias
                                { symbolOrAliasConstructor = testId "symbol2"
                                , symbolOrAliasParams = [ sort ]
                                }
                            []
                        )
                , sentenceAxiomAttributes = Attributes []
                }
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
            :: VerifiedKoreSentenceSymbol Object)
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
    symbolPattern =
        mkApp
            defaultSort
            SymbolOrAlias
                { symbolOrAliasConstructor = testId "symbol1"
                , symbolOrAliasParams = [ defaultSort ]
                }
            []
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
        :: VerifiedKoreSentenceSymbol Object)
    defaultSymbolSupportSentences = [ defaultSortDeclaration ]
    metaSymbolPattern =
        mkApp
            charMetaSort
            SymbolOrAlias
                { symbolOrAliasConstructor = testId "#symbol1"
                , symbolOrAliasParams = [ charMetaSort ]
                }
            []
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
        :: VerifiedKoreSentenceSymbol Meta)
    symbolReferenceInAxiomSentence =
        asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    toKorePattern symbolPattern
                , sentenceAxiomAttributes = Attributes []
                }
    metaSymbolReferenceInAxiomSentence =
        asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    toKorePattern metaSymbolPattern
                , sentenceAxiomAttributes = Attributes []
                }
    symbolReferenceInAndPatternSentence =
        asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    toKorePattern (mkAnd symbolPattern mkTop_)
                , sentenceAxiomAttributes = Attributes []
                }
    symbolReferenceInExistsPatternSentence =
        asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    toKorePattern
                        (mkExists
                            Variable
                                { variableName = testId "var"
                                , variableCounter = mempty
                                , variableSort = defaultSort
                                }
                            symbolPattern
                        )
                , sentenceAxiomAttributes = Attributes []
                }
    symbolReferenceInNextPatternSentence =
        asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    toKorePattern (mkNext symbolPattern)
                , sentenceAxiomAttributes = Attributes []
                }
    symbolReferenceInSymbolOrAliasSentence =
        asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    toKorePattern
                        (mkApp
                            defaultSort
                            SymbolOrAlias
                                { symbolOrAliasConstructor = testId "symbol2"
                                , symbolOrAliasParams = [ defaultSort ]
                                }
                            [symbolPattern]
                        )
                , sentenceAxiomAttributes = Attributes []
                }
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
            :: VerifiedKoreSentenceSymbol Object)
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
    aliasPattern =
        mkApp
            defaultSort
            SymbolOrAlias
                { symbolOrAliasConstructor = testId "alias1"
                , symbolOrAliasParams = [ defaultSort ]
                }
            []
    aliasDeclaration =
        let aliasConstructor = testId "alias1"
            aliasParams = [SortVariable (testId "sv1")]
            sentenceAliasResultSort :: Sort Object
            sentenceAliasResultSort =
                SortVariableSort (SortVariable (testId "sv1"))
        in (UnifiedObjectSentence . SentenceAliasSentence)
            SentenceAlias
                { sentenceAliasAlias = Alias { aliasConstructor, aliasParams }
                , sentenceAliasSorts = []
                , sentenceAliasResultSort
                , sentenceAliasLeftPattern  =
                    Application
                        { applicationSymbolOrAlias =
                            SymbolOrAlias
                                { symbolOrAliasConstructor = aliasConstructor
                                , symbolOrAliasParams =
                                    SortVariableSort <$> aliasParams
                                }
                        , applicationChildren = []
                        }
                , sentenceAliasRightPattern =
                    toKorePattern $ mkTop sentenceAliasResultSort
                , sentenceAliasAttributes = Attributes []
                }
    defaultAliasSupportSentences = [ defaultSortDeclaration ]
    metaAliasPattern =
        mkApp
            charMetaSort
            SymbolOrAlias
                { symbolOrAliasConstructor = testId "#alias1"
                , symbolOrAliasParams = [ charMetaSort ]
                }
            []
    metaAliasDeclaration =
        let aliasConstructor = testId "#alias1"
            aliasParams = [SortVariable (testId "#sv1")]
            symbolOrAliasParams = SortVariableSort <$> aliasParams
            sentenceAliasResultSort :: Sort Meta
            sentenceAliasResultSort =
                SortVariableSort (SortVariable (testId "#sv1"))
        in (UnifiedObjectSentence . SentenceAliasSentence)
            SentenceAlias
                { sentenceAliasAlias = Alias { aliasConstructor, aliasParams }
                , sentenceAliasSorts = []
                , sentenceAliasResultSort
                , sentenceAliasLeftPattern  =
                    Application
                        { applicationSymbolOrAlias =
                            SymbolOrAlias
                                { symbolOrAliasConstructor = aliasConstructor
                                , symbolOrAliasParams
                                }
                        , applicationChildren = []
                        }
                , sentenceAliasRightPattern =
                    toKorePattern $ mkTop sentenceAliasResultSort
                , sentenceAliasAttributes = Attributes []
                }
    aliasReferenceInAxiomSentence =
        asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = toKorePattern aliasPattern
                , sentenceAxiomAttributes = Attributes []
                }
    metaAliasReferenceInAxiomSentence =
        asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = toKorePattern metaAliasPattern
                , sentenceAxiomAttributes = Attributes []
                }
    aliasReferenceInAndPatternSentence =
        asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    toKorePattern
                        (mkAnd aliasPattern mkTop_)
                , sentenceAxiomAttributes = Attributes []
                }
    aliasReferenceInExistsPatternSentence =
        asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    toKorePattern
                        (mkExists
                            Variable
                                { variableName = testId "var"
                                , variableCounter = mempty
                                , variableSort = defaultSort
                                }
                            aliasPattern
                        )
                , sentenceAxiomAttributes = Attributes []
                }
    aliasReferenceInNextPatternSentence =
        asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    toKorePattern (mkNext aliasPattern)
                , sentenceAxiomAttributes = Attributes []
                }
    aliasReferenceInAliasOrAliasSentence =
        asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    toKorePattern
                        (mkApp
                            defaultSort
                            SymbolOrAlias
                                { symbolOrAliasConstructor = testId "alias2"
                                , symbolOrAliasParams = [ defaultSort ]
                                }
                            [aliasPattern]
                        )
                , sentenceAxiomAttributes = Attributes []
                }
    aliasReferenceInAliasOrAliasSupportSentences
        :: [VerifiedKoreSentence]
    aliasReferenceInAliasOrAliasSupportSentences =
        let aliasConstructor :: Id Object
            aliasConstructor = testId "alias2" :: Id Object
            aliasParams = [SortVariable (testId "sv1")]
            sentenceAliasResultSort :: Sort Object
            sentenceAliasResultSort =
                SortVariableSort (SortVariable (testId "sv1"))
        in (toKoreSentence . SentenceAliasSentence)
            SentenceAlias
                { sentenceAliasAlias = Alias { aliasConstructor, aliasParams }
                , sentenceAliasSorts =
                    [ SortVariableSort (SortVariable (testId "sv1")) ]
                , sentenceAliasResultSort
                , sentenceAliasLeftPattern  =
                    Application
                        { applicationSymbolOrAlias =
                            SymbolOrAlias
                                { symbolOrAliasConstructor = testId "alias2"
                                , symbolOrAliasParams =
                                    [ SortVariableSort
                                        (SortVariable (testId "sv1"))
                                    ]
                                }
                        , applicationChildren =
                            [ Variable
                                { variableName = testId "x"
                                , variableCounter = mempty
                                , variableSort =
                                    SortVariableSort
                                        (SortVariable (testId "sv1"))
                                }
                            ]
                        }
                , sentenceAliasRightPattern = mkTop sentenceAliasResultSort
                , sentenceAliasAttributes = Attributes []
                }
        : defaultAliasSupportSentences


defaultSort :: Sort Object
defaultSort = SortActualSort SortActual
    { sortActualName = testId "sort1"
    , sortActualSorts = []
    }

defaultSortDeclaration :: VerifiedKoreSentence
defaultSortDeclaration = asSentence
    (SentenceSort
        { sentenceSortName = testId "sort1"
        , sentenceSortParameters = []
        , sentenceSortAttributes = Attributes []
        }
    :: VerifiedKoreSentenceSort Object)

newtype DeclaringSentence = DeclaringSentence VerifiedKoreSentence
newtype UsingSentence = UsingSentence VerifiedKoreSentence
newtype SupportingSentences = SupportingSentences [VerifiedKoreSentence]

nameReferenceTests
    :: HasCallStack
    => String
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
    :: HasCallStack
    => DeclaringSentence
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
    :: HasCallStack
    => ExpectedErrorMessage
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
                    :: VerifiedKoreSentenceSort Object)
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
                    :: VerifiedKoreSentenceSymbol Object)
                ]
            , moduleAttributes = Attributes []
            }
    aliasDeclarationModule modName (AliasName aliasName) =
        let sv1 = SortVariable (testId "sv1") :: SortVariable Object
            aliasConstructor = testId aliasName :: Id Object
        in Module
            { moduleName = modName
            , moduleSentences =
                [ (toKoreSentence . asSentence)
                    SentenceAlias
                        { sentenceAliasAlias = Alias
                            { aliasConstructor
                            , aliasParams = [sv1]
                            }
                        , sentenceAliasSorts = []
                        , sentenceAliasResultSort = SortVariableSort sv1
                        , sentenceAliasLeftPattern =
                            Application
                                { applicationSymbolOrAlias =
                                    SymbolOrAlias
                                        { symbolOrAliasConstructor =
                                            aliasConstructor
                                        , symbolOrAliasParams =
                                            [SortVariableSort sv1]
                                        }
                                , applicationChildren = []
                                }
                        , sentenceAliasRightPattern =
                            mkTop (SortVariableSort sv1)
                        , sentenceAliasAttributes = Attributes []
                        }
                ]
            , moduleAttributes = Attributes []
            }

duplicatedNameFailureTest
    :: String -> String -> VerifiedKoreModule -> VerifiedKoreModule -> TestTree
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
