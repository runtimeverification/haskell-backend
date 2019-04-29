module Test.Kore.ASTVerifier.DefinitionVerifier.Imports
    ( test_imports
    ) where

import Test.Tasty
       ( TestTree, testGroup )

import GHC.Stack
       ( HasCallStack )

import           Kore.AST.Pure
import           Kore.AST.Sentence
import           Kore.AST.Valid
import           Kore.Error
import           Kore.IndexedModule.Error
                 ( noSort )
import qualified Kore.Verified as Verified

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
        (ExpectedErrorMessage $ noSort "sort1")
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
        (ExpectedErrorMessage $ noSort "sort1")
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
        (ExpectedErrorMessage $ noSort "sort1")
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
        (ExpectedErrorMessage $ noSort "sort1")
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
        (ExpectedErrorMessage $ noSort "sort1")
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
        (ExpectedErrorMessage $ noSort "sort1")
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
        (ExpectedErrorMessage $ noSort "sort1")
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
        (ExpectedErrorMessage $ noSort "sort1")
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
        (ExpectedErrorMessage $ noSort "sort1")
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
        (ExpectedErrorMessage $ noSort "sort1")
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
        (ExpectedErrorMessage $ noSort "sort1")
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
        :: Verified.SentenceSort)
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
        :: Verified.SentenceSort)
    topSortPattern = mkTop sort
    metaTopSortPattern = mkTop charMetaSort
    sortReferenceInSort =
        SortActualSort SortActual
            { sortActualName = testId "sort2"
            , sortActualSorts = [ sort ]
            } :: Sort Object
    sortReferenceInSortSentence =
        SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    mkTop sortReferenceInSort
                , sentenceAxiomAttributes = Attributes []
                }
    sortReferenceInSortSupportingSentences =
        [ asSentence
            (SentenceSort
                { sentenceSortName = testId "sort2"
                , sentenceSortParameters = [SortVariable (testId "x")]
                , sentenceSortAttributes = Attributes []
                }
            :: Verified.SentenceSort)
        ]
    sortReferenceInTopPatternSentence =
        SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = topSortPattern
                , sentenceAxiomAttributes = Attributes []
                }
    metaSortReferenceInTopPatternSentence =
        SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = metaTopSortPattern
                , sentenceAxiomAttributes = Attributes []
                }
    sortReferenceInExistsPatternSentence =
        SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
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
        SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    mkAnd (mkTop sort) mkTop_
                , sentenceAxiomAttributes = Attributes []
                }
    sortReferenceInNextPatternSentence =
        SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                        (mkNext (mkTop sort))
                , sentenceAxiomAttributes = Attributes []
                }
    sortReferenceInPatternInPatternSentence =
        SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
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
            :: Verified.SentenceSymbol)
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
            :: Verified.SentenceSymbol)
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
                    mkTop sort
                , sentenceAliasAttributes = Attributes []
                }
            :: Verified.SentenceAlias)
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
                    mkTop anotherSort
                , sentenceAliasAttributes = Attributes []
                }
            :: Verified.SentenceAlias)
    sortReferenceInSentenceAliasSortsSupportSentences =
        [ anotherSortDeclaration ]
    sortReferenceInSymbolOrAliasSentence =
        SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
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
            :: Verified.SentenceSymbol)
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
        :: Verified.SentenceSymbol)
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
        :: Verified.SentenceSymbol)
    symbolReferenceInAxiomSentence =
        SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    symbolPattern
                , sentenceAxiomAttributes = Attributes []
                }
    metaSymbolReferenceInAxiomSentence =
        SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    metaSymbolPattern
                , sentenceAxiomAttributes = Attributes []
                }
    symbolReferenceInAndPatternSentence =
        SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    (mkAnd symbolPattern mkTop_)
                , sentenceAxiomAttributes = Attributes []
                }
    symbolReferenceInExistsPatternSentence =
        SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
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
        SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    (mkNext symbolPattern)
                , sentenceAxiomAttributes = Attributes []
                }
    symbolReferenceInSymbolOrAliasSentence =
        SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
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
            :: Verified.SentenceSymbol)
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
        in SentenceAliasSentence
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
                    mkTop sentenceAliasResultSort
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
        in SentenceAliasSentence
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
                    mkTop sentenceAliasResultSort
                , sentenceAliasAttributes = Attributes []
                }
    aliasReferenceInAxiomSentence =
        SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = aliasPattern
                , sentenceAxiomAttributes = Attributes []
                }
    metaAliasReferenceInAxiomSentence =
        SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern = metaAliasPattern
                , sentenceAxiomAttributes = Attributes []
                }
    aliasReferenceInAndPatternSentence =
        SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                        (mkAnd aliasPattern mkTop_)
                , sentenceAxiomAttributes = Attributes []
                }
    aliasReferenceInExistsPatternSentence =
        SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
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
        SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    (mkNext aliasPattern)
                , sentenceAxiomAttributes = Attributes []
                }
    aliasReferenceInAliasOrAliasSentence =
        SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = []
                , sentenceAxiomPattern =
                    mkApp
                        defaultSort
                        SymbolOrAlias
                            { symbolOrAliasConstructor = testId "alias2"
                            , symbolOrAliasParams = [ defaultSort ]
                            }
                        [aliasPattern]
                , sentenceAxiomAttributes = Attributes []
                }
    aliasReferenceInAliasOrAliasSupportSentences
        :: [Verified.Sentence]
    aliasReferenceInAliasOrAliasSupportSentences =
        let aliasConstructor :: Id
            aliasConstructor = testId "alias2" :: Id
            aliasParams = [SortVariable (testId "sv1")]
            sentenceAliasResultSort :: Sort Object
            sentenceAliasResultSort =
                SortVariableSort (SortVariable (testId "sv1"))
        in SentenceAliasSentence
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

defaultSortDeclaration :: Verified.Sentence
defaultSortDeclaration = asSentence
    (SentenceSort
        { sentenceSortName = testId "sort1"
        , sentenceSortParameters = []
        , sentenceSortAttributes = Attributes []
        }
    :: Verified.SentenceSort)

newtype DeclaringSentence = DeclaringSentence Verified.Sentence
newtype UsingSentence = UsingSentence Verified.Sentence
newtype SupportingSentences = SupportingSentences [Verified.Sentence]

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
                    :: Verified.SentenceSort)
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
                    :: Verified.SentenceSymbol)
                ]
            , moduleAttributes = Attributes []
            }
    aliasDeclarationModule modName (AliasName aliasName) =
        let sv1 = SortVariable (testId "sv1") :: SortVariable Object
            aliasConstructor = testId aliasName :: Id
        in Module
            { moduleName = modName
            , moduleSentences =
                [ asSentence
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
    :: String
    -> String
    -> Module Verified.Sentence
    -> Module Verified.Sentence
    -> TestTree
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
