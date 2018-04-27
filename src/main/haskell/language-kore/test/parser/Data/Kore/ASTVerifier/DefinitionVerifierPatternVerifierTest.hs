module Data.Kore.ASTVerifier.DefinitionVerifierPatternVerifierTest
    (definitionVerifierPatternVerifierTests) where

import           Test.Tasty                                          (TestTree,
                                                                      testGroup)

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.ASTVerifier.DefinitionVerifierTestHelpers as Helpers
import           Data.Kore.Building.Implicit
import           Data.Kore.Building.Patterns                         as Patterns
import           Data.Kore.Error
import           Data.Kore.Implicit.ImplicitSorts

import qualified Data.List                                           as List

data PatternRestrict
    = NeedsSortVariables
    | NeedsInternalDefinitions
    | NeedsSortedParent
    | NoRestrict

data TestPattern level = TestPattern
    { testPatternPattern    :: Pattern level Variable UnifiedPattern
    , testPatternErrorStack :: ErrorStack
    }

newtype VariableOfDeclaredSort level = VariableOfDeclaredSort (Variable level)

testPatternErrorStackStrings :: TestPattern level -> [String]
testPatternErrorStackStrings
    TestPattern {testPatternErrorStack = ErrorStack strings}
  =
    strings

testPatternUnifiedPattern
    :: MetaOrObject level => TestPattern level -> UnifiedPattern
testPatternUnifiedPattern
    TestPattern {testPatternPattern = p}
  =
    asUnifiedPattern p

definitionVerifierPatternVerifierTests :: TestTree
definitionVerifierPatternVerifierTests =
    testGroup
        "Definition verifier - pattern usage - unit tests"
        [ expectSuccess "Simplest definition"
            (simpleDefinitionFromSentences (ModuleName "MODULE") [])
        , successTestsForObjectPattern "Simple object pattern"
            (simpleExistsPattern objectVariable objectSort)
            (NamePrefix "dummy")
            (TestedPatternSort objectSort)
            (SortVariablesThatMustBeDeclared [])
            (DeclaredSort anotherSort)
            [objectSortSentence, anotherSortSentence]
            NeedsInternalDefinitions
        , successTestsForMetaPattern "Simple meta pattern"
            (simpleExistsPattern metaVariable metaSort1)
            (NamePrefix "#dummy")
            (TestedPatternSort metaSort1)
            (SortVariablesThatMustBeDeclared [])
            (SortVariablesThatMustBeDeclared [])
            (DeclaredSort anotherMetaSort)
            (VariableOfDeclaredSort dummyMetaVariable)
            []
            -- TODO: Here we should be able to use NoRestrict,
            -- at least in some cases.
            NeedsInternalDefinitions
        , successTestsForMetaPattern "implicit meta pattern"
            (asMetaPattern metaNilSortList)
            (NamePrefix "#dummy")
            (TestedPatternSort sortListMetaSort)
            (SortVariablesThatMustBeDeclared [])
            (SortVariablesThatMustBeDeclared [])
            (DeclaredSort anotherMetaSort)
            (VariableOfDeclaredSort dummyMetaVariable)
            []
            -- TODO: Here we should be able to use NoRestrict,
            -- at least in some cases.
            NeedsInternalDefinitions
        , failureTestsForObjectPattern "Object pattern - sort not defined"
            (ExpectedErrorMessage "Sort 'ObjectSort' not declared.")
            (ErrorStack
                [ "\\exists 'ObjectVariable'"
                , "\\exists 'ObjectVariable'"
                , "sort 'ObjectSort'"
                ]
            )
            (ExistsPattern Exists
                { existsSort = anotherSort
                , existsVariable = anotherVariable
                , existsChild =
                    ObjectPattern
                        (simpleExistsPattern objectVariable objectSort)
                }
            )
            (NamePrefix "dummy")
            (TestedPatternSort anotherSort)
            (SortVariablesThatMustBeDeclared [])
            (DeclaredSort anotherSort)
            [anotherSortSentence]
            NeedsInternalDefinitions
        , failureTestsForObjectPattern
            "Object pattern - different variable sort"
            (ExpectedErrorMessage "The declared sort is different.")
            (ErrorStack
                [ "\\exists 'ObjectVariable'"
                , "variable 'ObjectVariable'"
                ]
            )
            (ExistsPattern Exists
                { existsSort = objectSort
                , existsVariable = objectVariable
                , existsChild =
                    ObjectPattern (VariablePattern anotherVariable)
                }
            )
            (NamePrefix "dummy")
            (TestedPatternSort objectSort)
            (SortVariablesThatMustBeDeclared [])
            (DeclaredSort anotherSort)
            [objectSortSentence, anotherSortSentence]
            NeedsInternalDefinitions
        , successTestsForObjectPattern
            "Object pattern - sort variable defined"
            (simpleExistsPattern
                objectVariableSortVariable objectSortVariableSort)
            (NamePrefix "dummy")
            (TestedPatternSort objectSortVariableSort)
            (SortVariablesThatMustBeDeclared [objectSortVariable])
            (DeclaredSort anotherSort)
            [anotherSortSentence]
            NeedsSortVariables
        , failureTestsForObjectPattern
            "Object pattern - sort variable not defined"
            (ExpectedErrorMessage
                "Sort variable 'ObjectSortVariable' not declared.")
            (ErrorStack
                [ "\\exists 'ObjectVariable'"
                , "\\exists 'ObjectVariable'"
                ]
            )
            (ExistsPattern Exists
                { existsSort = objectSort
                , existsVariable = objectVariable
                , existsChild =
                    ObjectPattern
                        (simpleExistsPattern
                            objectVariableSortVariable objectSortVariableSort)
                }
            )
            (NamePrefix "dummy")
            (TestedPatternSort objectSort)
            (SortVariablesThatMustBeDeclared [])
            (DeclaredSort anotherSort)
            [objectSortSentence, anotherSortSentence]
            NeedsSortVariables
        , failureTestsForMetaPattern "Meta pattern - sort not defined"
            (ExpectedErrorMessage "Sort '#InvalidMetaSort' not declared.")
            (ErrorStack
                [ "\\exists '#MetaVariable'"
                , "sort '#InvalidMetaSort'"
                ]
            )
            (simpleExistsPattern metaVariable invalidMetaSort)
            (NamePrefix "#dummy")
            (TestedPatternSort metaSort1)
            (SortVariablesThatMustBeDeclared [])
            (SortVariablesThatMustBeDeclared [])
            (DeclaredSort anotherMetaSort)
            (VariableOfDeclaredSort dummyMetaVariable)
            []
            NeedsInternalDefinitions
        , failureTestsForObjectPattern "Object pattern - sort not matched"
            (ExpectedErrorMessage
                "Expecting sort 'anotherSort2{}' but got 'ObjectSort{}'.")
            (ErrorStack
                [ "\\exists 'ObjectVariable'"
                , "variable 'ObjectVariable'"
                ]
            )
            (simpleExistsPattern objectVariable anotherObjectSort2)
            (NamePrefix "dummy")
            (TestedPatternSort objectSort)
            (SortVariablesThatMustBeDeclared [])
            (DeclaredSort anotherSort)
            [ objectSortSentence
            , anotherSortSentence
            , anotherObjectSortSentence2
            ]
            NeedsInternalDefinitions
        , failureTestsForMetaPattern "Meta pattern - sort not matched"
            (ExpectedErrorMessage
                "Expecting sort '#Variable{}' but got '#CharList{}'.")
            (ErrorStack
                [ "\\exists '#MetaVariable'"
                , "variable '#MetaVariable'"
                ]
            )
            (simpleExistsPattern metaVariable anotherMetaSort2)
            (NamePrefix "#dummy")
            (TestedPatternSort metaSort1)
            (SortVariablesThatMustBeDeclared [])
            (SortVariablesThatMustBeDeclared [])
            (DeclaredSort anotherMetaSort)
            (VariableOfDeclaredSort dummyMetaVariable)
            []
            NeedsInternalDefinitions
        , successTestsForObjectPattern "Application pattern - symbol"
            (applicationPatternWithChildren
                objectSymbolName
                [ simpleExistsObjectUnifiedPattern
                    objectVariableName anotherObjectSort2]
            )
            (NamePrefix "dummy")
            (TestedPatternSort objectSort)
            (SortVariablesThatMustBeDeclared [])
            (DeclaredSort anotherSort)
            [ objectSortSentence
            , anotherSortSentence
            , anotherObjectSortSentence2
            , objectSymbolSentence
            ]
            NeedsInternalDefinitions
        , successTestsForObjectPattern "Application pattern - alias"
            (applicationPatternWithChildren
                objectAliasNameAsSymbol
                [ simpleExistsObjectUnifiedPattern
                    objectVariableName anotherObjectSort2]
            )
            (NamePrefix "dummy")
            (TestedPatternSort objectSort)
            (SortVariablesThatMustBeDeclared [])
            (DeclaredSort anotherSort)
            [ objectSortSentence
            , anotherSortSentence
            , anotherObjectSortSentence2
            , objectAliasSentence
            ]
            NeedsInternalDefinitions
        , failureTestsForObjectPattern
            "Application pattern - symbol not declared"
            (ExpectedErrorMessage "Symbol 'ObjectSymbol' not defined.")
            (ErrorStack ["symbol or alias 'ObjectSymbol'"])
            (applicationPatternWithChildren
                objectSymbolName
                [ simpleExistsObjectUnifiedPattern
                    objectVariableName anotherObjectSort2]
            )
            (NamePrefix "dummy")
            (TestedPatternSort objectSort)
            (SortVariablesThatMustBeDeclared [])
            (DeclaredSort anotherSort)
            [ objectSortSentence
            , anotherSortSentence
            , anotherObjectSortSentence2
            --, objectSymbolSentence
            ]
            NeedsInternalDefinitions
        , failureTestsForObjectPattern
            "Application pattern - not enough arguments"
            (ExpectedErrorMessage "Expected 1 operands, but got 0.")
            (ErrorStack ["symbol or alias 'ObjectSymbol'"])
            (applicationPatternWithChildren objectSymbolName [])
            (NamePrefix "dummy")
            (TestedPatternSort objectSort)
            (SortVariablesThatMustBeDeclared [])
            (DeclaredSort anotherSort)
            [ objectSortSentence
            , anotherSortSentence
            , anotherObjectSortSentence2
            , objectSymbolSentence
            ]
            NeedsInternalDefinitions
        , failureTestsForObjectPattern "Object pattern - too many arguments"
            (ExpectedErrorMessage "Expected 1 operands, but got 2.")
            (ErrorStack ["symbol or alias 'ObjectSymbol'"])
            (applicationPatternWithChildren
                objectSymbolName
                [ simpleExistsObjectUnifiedPattern
                    objectVariableName anotherObjectSort2
                , simpleExistsObjectUnifiedPattern
                    objectVariableName anotherObjectSort2
                ]
            )
            (NamePrefix "dummy")
            (TestedPatternSort objectSort)
            (SortVariablesThatMustBeDeclared [])
            (DeclaredSort anotherSort)
            [ objectSortSentence
            , anotherSortSentence
            , anotherObjectSortSentence2
            , objectSymbolSentence
            ]
            NeedsInternalDefinitions
        , failureTestsForObjectPattern
            "Object pattern alias - too many arguments"
            (ExpectedErrorMessage "Expected 1 operands, but got 2.")
            (ErrorStack ["symbol or alias 'ObjectAlias'"])
            (applicationPatternWithChildren
                objectAliasNameAsSymbol
                [ simpleExistsObjectUnifiedPattern
                    objectVariableName anotherObjectSort2
                , simpleExistsObjectUnifiedPattern
                    objectVariableName anotherObjectSort2
                ]
            )
            (NamePrefix "dummy")
            (TestedPatternSort objectSort)
            (SortVariablesThatMustBeDeclared [])
            (DeclaredSort anotherSort)
            [ objectSortSentence
            , anotherSortSentence
            , anotherObjectSortSentence2
            , objectAliasSentence
            ]
            NeedsInternalDefinitions
        , failureTestsForMetaPattern "Meta pattern - wrong argument count"
            (ExpectedErrorMessage "Expected 1 operands, but got 0.")
            (ErrorStack ["symbol or alias '#MetaSymbol'"])
            (applicationPatternWithChildren metaSymbolName [])
            (NamePrefix "#dummy")
            (TestedPatternSort metaSort1)
            (SortVariablesThatMustBeDeclared [])
            (SortVariablesThatMustBeDeclared [])
            (DeclaredSort anotherMetaSort)
            (VariableOfDeclaredSort dummyMetaVariable)
            [ metaSymbolSentence ]
            NeedsInternalDefinitions
        , failureTestsForObjectPattern "Application pattern - too few sorts"
            (ExpectedErrorMessage
                "Application uses less sorts than the declaration.")
            (ErrorStack ["symbol or alias 'ObjectSymbol'"])
            (ApplicationPattern Application
                { applicationSymbolOrAlias = SymbolOrAlias
                    { symbolOrAliasConstructor = Id oneSortSymbolRawName
                    , symbolOrAliasParams = []
                    }
                , applicationChildren =
                    [ simpleExistsObjectUnifiedPattern
                        objectVariableName anotherObjectSort2]
                }
            )
            (NamePrefix "dummy")
            (TestedPatternSort objectSort)
            (SortVariablesThatMustBeDeclared [])
            (DeclaredSort anotherSort)
            [ objectSortSentence
            , anotherSortSentence
            , anotherObjectSortSentence2
            , oneSortSymbolSentence
            ]
            NeedsInternalDefinitions
        , failureTestsForObjectPattern "Application pattern - too many sorts"
            (ExpectedErrorMessage
                "Application uses more sorts than the declaration.")
            (ErrorStack ["symbol or alias 'ObjectSymbol'"])
            (ApplicationPattern Application
                { applicationSymbolOrAlias = SymbolOrAlias
                    { symbolOrAliasConstructor = Id oneSortSymbolRawName
                    , symbolOrAliasParams = [objectSort, objectSort]
                    }
                , applicationChildren =
                    [ simpleExistsObjectUnifiedPattern
                        objectVariableName anotherObjectSort2]
                }
            )
            (NamePrefix "dummy")
            (TestedPatternSort objectSort)
            (SortVariablesThatMustBeDeclared [])
            (DeclaredSort anotherSort)
            [ objectSortSentence
            , anotherSortSentence
            , anotherObjectSortSentence2
            , oneSortSymbolSentence
            ]
            NeedsInternalDefinitions
        , successTestsForObjectPattern "Object pattern - unquantified variable"
            (VariablePattern objectVariable)
            (NamePrefix "dummy")
            (TestedPatternSort objectSort)
            (SortVariablesThatMustBeDeclared [])
            (DeclaredSort anotherSort)
            [ objectSortSentence, anotherSortSentence ]
            NeedsInternalDefinitions
        , successTestsForMetaPattern "Meta pattern - unquantified variable"
            (VariablePattern metaVariable)
            (NamePrefix "#dummy")
            (TestedPatternSort metaSort1)
            (SortVariablesThatMustBeDeclared [])
            (SortVariablesThatMustBeDeclared [])
            (DeclaredSort anotherMetaSort)
            (VariableOfDeclaredSort dummyMetaVariable)
            []
            NeedsInternalDefinitions
        , successTestsForMetaPattern "Simple string pattern"
            (StringLiteralPattern (StringLiteral "MetaString"))
            (NamePrefix "#dummy")
            (TestedPatternSort charListMetaSort)
            (SortVariablesThatMustBeDeclared [])
            (SortVariablesThatMustBeDeclared [])
            (DeclaredSort anotherMetaSort)
            (VariableOfDeclaredSort dummyMetaVariable)
            []
            -- TODO: Here we should be able to use NoRestrict,
            -- at least in some cases.
            NeedsInternalDefinitions
        , successTestsForMetaPattern "Simple char pattern"
            (CharLiteralPattern (CharLiteral 'c'))
            (NamePrefix "#dummy")
            (TestedPatternSort charMetaSort)
            (SortVariablesThatMustBeDeclared [])
            (SortVariablesThatMustBeDeclared [])
            (DeclaredSort anotherMetaSort)
            (VariableOfDeclaredSort dummyMetaVariable)
            []
            -- TODO: Here we should be able to use NoRestrict,
            -- at least in some cases.
            NeedsInternalDefinitions
        , failureTestsForMetaPattern "String pattern - sort not matched"
            (ExpectedErrorMessage
                "Expecting sort '#Char{}' but got '#CharList{}'.")
            (ErrorStack ["<string>"])
            (StringLiteralPattern (StringLiteral "MetaString"))
            (NamePrefix "#dummy")
            (TestedPatternSort charMetaSort)
            (SortVariablesThatMustBeDeclared [])
            (SortVariablesThatMustBeDeclared [])
            (DeclaredSort anotherMetaSort)
            (VariableOfDeclaredSort dummyMetaVariable)
            []
            -- TODO: Here we should be able to use NoRestrict,
            -- at least in some cases.
            NeedsSortedParent
        , successTestsForObjectPattern "Bottom pattern"
            (BottomPattern Bottom {bottomSort = objectSort})
            (NamePrefix "dummy")
            (TestedPatternSort objectSort)
            (SortVariablesThatMustBeDeclared [])
            (DeclaredSort anotherSort)
            [ objectSortSentence
            , anotherSortSentence
            ]
            NeedsInternalDefinitions
        , successTestsForObjectPattern "Top pattern"
            (TopPattern Top {topSort = objectSort})
            (NamePrefix "dummy")
            (TestedPatternSort objectSort)
            (SortVariablesThatMustBeDeclared [])
            (DeclaredSort anotherSort)
            [ objectSortSentence
            , anotherSortSentence
            ]
            NeedsInternalDefinitions
        ]
  where
    objectSortName = SortName "ObjectSort"
    objectSort = simpleSort objectSortName
    objectVariableName = VariableName "ObjectVariable"
    objectVariable = variable objectVariableName objectSort
    objectSortSentence = simpleSortSentence objectSortName
    metaSort1 = charListMetaSort
    metaVariable = variable (VariableName "#MetaVariable") metaSort1
    dummyMetaSort = patternMetaSort
    dummyMetaVariable = variable (VariableName "#otherVariable") dummyMetaSort
    anotherSortName = SortName "anotherSort"
    anotherSort = simpleSort anotherSortName
    anotherVariable = variable objectVariableName anotherSort
    anotherSortSentence = simpleSortSentence anotherSortName
    anotherMetaSort = symbolMetaSort
    anotherObjectSortName2 = SortName "anotherSort2"
    anotherObjectSort2 = simpleSort anotherObjectSortName2
    anotherObjectSortSentence2 = simpleSortSentence anotherObjectSortName2
    invalidMetaSort = simpleSort (SortName "#InvalidMetaSort")
    anotherMetaSort2 = variableMetaSort
    objectSymbolName = SymbolName "ObjectSymbol"
    objectSymbolSentence =
        objectSymbolSentenceWithArguments
            objectSymbolName objectSort [anotherObjectSort2]
    metaSymbolName = SymbolName "#MetaSymbol"
    metaSymbolSentence =
        symbolSentenceWithArguments
            metaSymbolName metaSort1 [anotherMetaSort2]
    objectAliasName = AliasName "ObjectAlias"
    objectAliasNameAsSymbol = SymbolName "ObjectAlias"
    objectAliasSentence =
        objectAliasSentenceWithArguments
            objectAliasName objectSort [anotherObjectSort2]
    objectSortVariableName = SortVariableName "ObjectSortVariable"
    objectSortVariable = sortVariable Object objectSortVariableName
    objectSortVariableSort = sortVariableSort objectSortVariableName
    objectVariableSortVariable =
        variable objectVariableName objectSortVariableSort
    oneSortSymbolRawName = "ObjectSymbol"
    oneSortSymbolSentence =
        ObjectSentence . SentenceSymbolSentence
        $ SentenceSymbol
            { sentenceSymbolSymbol = Symbol
                { symbolConstructor = Id oneSortSymbolRawName
                , symbolParams = [objectSortVariable]
                }
            , sentenceSymbolSorts = [anotherObjectSort2]
            , sentenceSymbolResultSort = objectSort
            , sentenceSymbolAttributes = Attributes []
            }

dummyVariableAndSentences :: NamePrefix -> (Variable Object, [KoreSentence])
dummyVariableAndSentences (NamePrefix namePrefix) =
    (dummyVariable, [simpleSortSentence dummySortName])
  where
    dummySortName = SortName (namePrefix ++ "_OtherSort")
    dummySort = simpleSort dummySortName
    dummyVariable =
        variable (VariableName (namePrefix ++ "_OtherVariable")) dummySort


successTestsForObjectPattern
    :: String
    -> Pattern Object Variable UnifiedPattern
    -> NamePrefix
    -> TestedPatternSort Object
    -> SortVariablesThatMustBeDeclared Object
    -> DeclaredSort Object
    -> [KoreSentence]
    -> PatternRestrict
    -> TestTree
successTestsForObjectPattern
    description
    testedPattern
    namePrefix
    testedSort
    sortVariables
    anotherSort
    sentences
    patternRestrict
  =
    successTestDataGroup description testData
  where
    (dummyVariable, dummySortSentences) =
        dummyVariableAndSentences namePrefix
    testData =
        genericPatternInAllContexts
            Object
            testedPattern
            namePrefix
            testedSort
            sortVariables
            sortVariables
            anotherSort
            (VariableOfDeclaredSort dummyVariable)
            (dummySortSentences ++ sentences)
            patternRestrict
        ++ objectPatternInAllContexts
            testedPattern
            namePrefix
            testedSort
            sortVariables
            anotherSort
            (dummySortSentences ++ sentences)
            patternRestrict

successTestsForMetaPattern
    :: String
    -> Pattern Meta Variable UnifiedPattern
    -> NamePrefix
    -> TestedPatternSort Meta
    -> SortVariablesThatMustBeDeclared Meta
    -> SortVariablesThatMustBeDeclared Object
    -> DeclaredSort Meta
    -> VariableOfDeclaredSort Meta
    -> [KoreSentence]
    -> PatternRestrict
    -> TestTree
successTestsForMetaPattern
    description
    testedPattern
    namePrefix
    testedSort
    sortVariables
    objectSortVariables
    anotherSort
    dummyVariable
    sentences
    patternRestrict
  =
    successTestDataGroup description testData
  where
    testData =
        genericPatternInAllContexts
            Meta
            testedPattern
            namePrefix
            testedSort
            sortVariables
            objectSortVariables
            anotherSort
            dummyVariable
            sentences
            patternRestrict

failureTestsForObjectPattern
    :: String
    -> ExpectedErrorMessage
    -> ErrorStack
    -> Pattern Object Variable UnifiedPattern
    -> NamePrefix
    -> TestedPatternSort Object
    -> SortVariablesThatMustBeDeclared Object
    -> DeclaredSort Object
    -> [KoreSentence]
    -> PatternRestrict
    -> TestTree
failureTestsForObjectPattern
    description
    errorMessage
    errorStackSuffix
    testedPattern
    namePrefix@(NamePrefix rawNamePrefix)
    testedSort
    sortVariables
    anotherSort
    sentences
    patternRestrict
  =
    failureTestDataGroup
        description
        errorMessage
        errorStackSuffix
        testData
  where
    dummySortName = SortName (rawNamePrefix ++ "_OtherSort")
    dummySort = simpleSort dummySortName
    dummyVariable =
        variable (VariableName (rawNamePrefix ++ "_OtherVariable")) dummySort
    dummySortSentence = simpleSortSentence dummySortName
    testData =
        genericPatternInAllContexts
            Object
            testedPattern
            namePrefix
            testedSort
            sortVariables
            sortVariables
            anotherSort
            (VariableOfDeclaredSort dummyVariable)
            (dummySortSentence : sentences)
            patternRestrict
        ++ objectPatternInAllContexts
            testedPattern
            namePrefix
            testedSort
            sortVariables
            anotherSort
            (dummySortSentence : sentences)
            patternRestrict

failureTestsForMetaPattern
    :: String
    -> ExpectedErrorMessage
    -> ErrorStack
    -> Pattern Meta Variable UnifiedPattern
    -> NamePrefix
    -> TestedPatternSort Meta
    -> SortVariablesThatMustBeDeclared Meta
    -> SortVariablesThatMustBeDeclared Object
    -> DeclaredSort Meta
    -> VariableOfDeclaredSort Meta
    -> [KoreSentence]
    -> PatternRestrict
    -> TestTree
failureTestsForMetaPattern
    description
    errorMessage
    errorStackSuffix
    testedPattern
    namePrefix
    testedSort
    sortVariables
    objectSortVariables
    anotherSort
    dummyVariable
    sentences
    patternRestrict
  =
    failureTestDataGroup
        description
        errorMessage
        errorStackSuffix
        testData
  where
    testData =
        genericPatternInAllContexts
            Meta
            testedPattern
            namePrefix
            testedSort
            sortVariables
            objectSortVariables
            anotherSort
            dummyVariable
            sentences
            patternRestrict

genericPatternInAllContexts
    :: MetaOrObject level
    => level
    -> Pattern level Variable UnifiedPattern
    -> NamePrefix
    -> TestedPatternSort level
    -> SortVariablesThatMustBeDeclared level
    -> SortVariablesThatMustBeDeclared Object
    -> DeclaredSort level
    -> VariableOfDeclaredSort level
    -> [KoreSentence]
    -> PatternRestrict
    -> [TestData]
genericPatternInAllContexts
    x
    testedPattern
    (NamePrefix namePrefix)
    (TestedPatternSort testedSort)
    sortVariables
    objectSortVariables
    (DeclaredSort anotherSort)
    dummyVariable
    sentences
    patternRestrict
  =
    patternsInAllContexts
        x
        patternExpansion
        (NamePrefix namePrefix)
        sortVariables
        objectSortVariables
        (DeclaredSort anotherSort)
        sentences
        patternRestrict
  where
    patternExpansion =
        genericPatternInPatterns
            testedPattern
            anotherPattern
            (OperandSort testedSort)
            (Helpers.ResultSort anotherSort)
            dummyVariable
            (symbolFromSort testedSort)
            (aliasFromSort testedSort)
            patternRestrict
    anotherPattern =
        ExistsPattern Exists
            { existsSort = testedSort
            , existsVariable = anotherVariable
            , existsChild = asUnifiedPattern (VariablePattern anotherVariable)
            }
    anotherVariable =
        Variable
            { variableName = Id (namePrefix ++ "_anotherVar")
            , variableSort = testedSort
            }
    rawSymbolName = namePrefix ++ "_anotherSymbol"
    rawAliasName = namePrefix ++ "_anotherAlias"
    symbolFromSort sort =
        SymbolOrAlias
            { symbolOrAliasConstructor = Id rawSymbolName
            , symbolOrAliasParams = [sort]
            }
    aliasFromSort sort =
        SymbolOrAlias
            { symbolOrAliasConstructor = Id rawAliasName
            , symbolOrAliasParams = [sort]
            }

objectPatternInAllContexts
    :: Pattern Object Variable UnifiedPattern
    -> NamePrefix
    -> TestedPatternSort Object
    -> SortVariablesThatMustBeDeclared Object
    -> DeclaredSort Object
    -> [KoreSentence]
    -> PatternRestrict
    -> [TestData]
objectPatternInAllContexts
    testedPattern
    (NamePrefix namePrefix)
    (TestedPatternSort testedSort)
    sortVariables
    (DeclaredSort anotherSort)
  =
    patternsInAllContexts
        Object
        patternExpansion
        (NamePrefix namePrefix)
        sortVariables
        sortVariables
        (DeclaredSort anotherSort)
  where
    patternExpansion =
        objectPatternInPatterns
            testedPattern
            anotherPattern
            (OperandSort testedSort)
    anotherPattern =
        ExistsPattern Exists
            { existsSort = testedSort
            , existsVariable = anotherVariable
            , existsChild = asUnifiedPattern (VariablePattern anotherVariable)
            }
    anotherVariable =
        Variable
            { variableName = Id (namePrefix ++ "_anotherVar")
            , variableSort = testedSort
            }

patternsInAllContexts
    :: MetaOrObject level
    => level
    -> [TestPattern level]
    -> NamePrefix
    -> SortVariablesThatMustBeDeclared level
    -> SortVariablesThatMustBeDeclared Object
    -> DeclaredSort level
    -> [KoreSentence]
    -> PatternRestrict
    -> [TestData]
patternsInAllContexts
    x
    patterns
    (NamePrefix namePrefix)
    sortVariables
    objectSortVariables
    (DeclaredSort anotherSort)
    sentences
    patternRestrict
  =
    map (\context -> context (List.head patterns)) contextExpansion
    ++ map (List.head contextExpansion) patterns
  where
    contextExpansion =
        testsForUnifiedPatternInTopLevelContext
            x
            (NamePrefix (namePrefix ++ "_piac"))
            (DeclaredSort anotherSort)
            sortVariables
            objectSortVariables
            ( symbolSentence
            : aliasSentence
            : sentences
            )
            patternRestrict
    rawSymbolName = namePrefix ++ "_anotherSymbol"
    rawAliasName = namePrefix ++ "_anotherAlias"
    rawSortVariableName = namePrefix ++ "_sortVariable"
    sortVariableName = SortVariableName rawSortVariableName
    symbolAliasSort = sortVariableSort sortVariableName
    symbolSentence =
        asKoreSymbolSentence SentenceSymbol
            { sentenceSymbolSymbol = Symbol
                { symbolConstructor = Id rawSymbolName
                , symbolParams = [SortVariable (Id rawSortVariableName)]
                }
            , sentenceSymbolSorts = [symbolAliasSort]
            , sentenceSymbolResultSort = anotherSort
            , sentenceSymbolAttributes = Attributes []
            }
    aliasSentence =
        asKoreAliasSentence SentenceAlias
            { sentenceAliasAlias = Alias
                { aliasConstructor = Id rawAliasName
                , aliasParams = [SortVariable (Id rawSortVariableName)]
                }
            , sentenceAliasSorts = [symbolAliasSort]
            , sentenceAliasResultSort = anotherSort
            , sentenceAliasAttributes = Attributes []
            }

genericPatternInPatterns
    :: MetaOrObject level
    => Pattern level Variable UnifiedPattern
    -> Pattern level Variable UnifiedPattern
    -> OperandSort level
    -> Helpers.ResultSort level
    -> VariableOfDeclaredSort level
    -> SymbolOrAlias level
    -> SymbolOrAlias level
    -> PatternRestrict
    -> [TestPattern level]
genericPatternInPatterns
    testedPattern
    anotherPattern
    sort@(OperandSort testedSort)
    resultSort
    (VariableOfDeclaredSort dummyVariable)
    symbol
    alias
    patternRestrict
  =
    patternInQuantifiedPatterns testedPattern testedSort dummyVariable
    ++ patternInUnquantifiedGenericPatterns
        testedPattern anotherPattern sort resultSort
    ++ case patternRestrict of
        NeedsSortedParent -> []
        _ ->
            [ TestPattern
                { testPatternPattern = testedPattern
                , testPatternErrorStack = ErrorStack []
                }
            ]
    ++
        [ TestPattern
            { testPatternPattern = ApplicationPattern Application
                { applicationSymbolOrAlias = symbol
                , applicationChildren = [asUnifiedPattern testedPattern]
                }
            , testPatternErrorStack =
                ErrorStack
                    [ "symbol or alias '"
                        ++ getId (symbolOrAliasConstructor symbol)
                        ++ "'"
                    ]
            }
        , TestPattern
            { testPatternPattern = ApplicationPattern Application
                { applicationSymbolOrAlias = alias
                , applicationChildren = [asUnifiedPattern testedPattern]
                }
            , testPatternErrorStack =
                ErrorStack
                    [ "symbol or alias '"
                        ++ getId (symbolOrAliasConstructor alias)
                        ++ "'"
                    ]
            }
        ]

objectPatternInPatterns
    :: Pattern Object Variable UnifiedPattern
    -> Pattern Object Variable UnifiedPattern
    -> OperandSort Object
    -> [TestPattern Object]
objectPatternInPatterns = patternInUnquantifiedObjectPatterns

patternInQuantifiedPatterns
    :: MetaOrObject level
    => Pattern level Variable UnifiedPattern
    -> Sort level
    -> Variable level
    -> [TestPattern level]
patternInQuantifiedPatterns testedPattern testedSort quantifiedVariable =
    [ TestPattern
        { testPatternPattern = ExistsPattern Exists
            { existsSort = testedSort
            , existsVariable = quantifiedVariable
            , existsChild = asUnifiedPattern testedPattern
            }
        , testPatternErrorStack =
            ErrorStack
                [ "\\exists '"
                    ++ getId (variableName quantifiedVariable)
                    ++ "'"
                ]
        }
    , TestPattern
        { testPatternPattern = ForallPattern Forall
            { forallSort = testedSort
            , forallVariable = quantifiedVariable
            , forallChild = asUnifiedPattern testedPattern
            }
        , testPatternErrorStack =
            ErrorStack
                [ "\\forall '"
                    ++ getId (variableName quantifiedVariable)
                    ++ "'"
                ]
        }
    ]

patternInUnquantifiedGenericPatterns
    :: MetaOrObject level
    => Pattern level Variable UnifiedPattern
    -> Pattern level Variable UnifiedPattern
    -> OperandSort level
    -> Helpers.ResultSort level
    -> [TestPattern level]
patternInUnquantifiedGenericPatterns
    testedPattern
    anotherPattern
    (OperandSort testedSort)
    (Helpers.ResultSort resultSort)
  =
    [ TestPattern
        { testPatternPattern = AndPattern And
            { andSort = testedSort
            , andFirst = testedUnifiedPattern
            , andSecond = anotherUnifiedPattern
            }
        , testPatternErrorStack = ErrorStack ["\\and"]
        }
    , TestPattern
        { testPatternPattern = AndPattern And
            { andSort = testedSort
            , andFirst = anotherUnifiedPattern
            , andSecond = testedUnifiedPattern
            }
        , testPatternErrorStack = ErrorStack ["\\and"]
        }
    , TestPattern
        { testPatternPattern = CeilPattern Ceil
            { ceilOperandSort = testedSort
            , ceilResultSort = resultSort
            , ceilChild = testedUnifiedPattern
            }
        , testPatternErrorStack = ErrorStack ["\\ceil"]
        }
    , TestPattern
        { testPatternPattern = EqualsPattern Equals
            { equalsOperandSort = testedSort
            , equalsResultSort = resultSort
            , equalsFirst = testedUnifiedPattern
            , equalsSecond = anotherUnifiedPattern
            }
        , testPatternErrorStack = ErrorStack ["\\equals"]
        }
    , TestPattern
        { testPatternPattern = EqualsPattern Equals
            { equalsOperandSort = testedSort
            , equalsResultSort = resultSort
            , equalsFirst = anotherUnifiedPattern
            , equalsSecond = testedUnifiedPattern
            }
        , testPatternErrorStack = ErrorStack ["\\equals"]
        }
    , TestPattern
        { testPatternPattern = FloorPattern Floor
            { floorOperandSort = testedSort
            , floorResultSort = resultSort
            , floorChild = testedUnifiedPattern
            }
        , testPatternErrorStack = ErrorStack ["\\floor"]
        }
    , TestPattern
        { testPatternPattern = IffPattern Iff
            { iffSort = testedSort
            , iffFirst = testedUnifiedPattern
            , iffSecond = anotherUnifiedPattern
            }
        , testPatternErrorStack = ErrorStack ["\\iff"]
        }
    , TestPattern
        { testPatternPattern = IffPattern Iff
            { iffSort = testedSort
            , iffFirst = anotherUnifiedPattern
            , iffSecond = testedUnifiedPattern
            }
        , testPatternErrorStack = ErrorStack ["\\iff"]
        }
    , TestPattern
        { testPatternPattern = ImpliesPattern Implies
            { impliesSort = testedSort
            , impliesFirst = testedUnifiedPattern
            , impliesSecond = anotherUnifiedPattern
            }
        , testPatternErrorStack = ErrorStack ["\\implies"]
        }
    , TestPattern
        { testPatternPattern = ImpliesPattern Implies
            { impliesSort = testedSort
            , impliesFirst = anotherUnifiedPattern
            , impliesSecond = testedUnifiedPattern
            }
        , testPatternErrorStack = ErrorStack ["\\implies"]
        }
    , TestPattern
        { testPatternPattern = InPattern In
            { inOperandSort = testedSort
            , inResultSort = resultSort
            , inContainedChild = testedUnifiedPattern
            , inContainingChild = anotherUnifiedPattern
            }
        , testPatternErrorStack = ErrorStack ["\\in"]
        }
    , TestPattern
        { testPatternPattern = InPattern In
            { inOperandSort = testedSort
            , inResultSort = resultSort
            , inContainedChild = anotherUnifiedPattern
            , inContainingChild = testedUnifiedPattern
            }
        , testPatternErrorStack = ErrorStack ["\\in"]
        }
    , TestPattern
        { testPatternPattern = NotPattern Not
            { notSort = testedSort
            , notChild = testedUnifiedPattern
            }
        , testPatternErrorStack = ErrorStack ["\\not"]
        }
    , TestPattern
        { testPatternPattern = OrPattern Or
            { orSort = testedSort
            , orFirst = testedUnifiedPattern
            , orSecond = anotherUnifiedPattern
            }
        , testPatternErrorStack = ErrorStack ["\\or"]
        }
    , TestPattern
        { testPatternPattern = OrPattern Or
            { orSort = testedSort
            , orFirst = anotherUnifiedPattern
            , orSecond = testedUnifiedPattern
            }
        , testPatternErrorStack = ErrorStack ["\\or"]
        }
    ]
  where
    anotherUnifiedPattern = asUnifiedPattern anotherPattern
    testedUnifiedPattern = asUnifiedPattern testedPattern

patternInUnquantifiedObjectPatterns
    :: Pattern Object Variable UnifiedPattern
    -> Pattern Object Variable UnifiedPattern
    -> OperandSort Object
    -> [TestPattern Object]
patternInUnquantifiedObjectPatterns
    testedPattern
    anotherPattern
    (OperandSort testedSort)
  =
    [ TestPattern
        { testPatternPattern = NextPattern Next
            { nextSort = testedSort
            , nextChild = testedUnifiedPattern
            }
        , testPatternErrorStack = ErrorStack ["\\next"]
        }
    , TestPattern
        { testPatternPattern = RewritesPattern Rewrites
            { rewritesSort = testedSort
            , rewritesFirst = testedUnifiedPattern
            , rewritesSecond = anotherUnifiedPattern
            }
        , testPatternErrorStack = ErrorStack ["\\rewrites"]
        }
    , TestPattern
        { testPatternPattern = RewritesPattern Rewrites
            { rewritesSort = testedSort
            , rewritesFirst = anotherUnifiedPattern
            , rewritesSecond = testedUnifiedPattern
            }
        , testPatternErrorStack = ErrorStack ["\\rewrites"]
        }

    ]
  where
    anotherUnifiedPattern = asUnifiedPattern anotherPattern
    testedUnifiedPattern = asUnifiedPattern testedPattern

testsForUnifiedPatternInTopLevelContext
    :: MetaOrObject level
    => level
    -> NamePrefix
    -> DeclaredSort level
    -> SortVariablesThatMustBeDeclared level
    -> SortVariablesThatMustBeDeclared Object
    -> [KoreSentence]
    -> PatternRestrict
    -> [TestPattern level -> TestData]
testsForUnifiedPatternInTopLevelContext
    x
    namePrefix
    additionalSort
    sortVariables
    objectSortVariables
    additionalSentences
    patternRestrict
  =
    testsForUnifiedPatternInTopLevelGenericContext
        x
        namePrefix
        additionalSort
        sortVariables
        additionalSentences
        patternRestrict
    ++ testsForUnifiedPatternInTopLevelObjectContext
        (SortName sortName)
        objectSortVariables
        additionalSentences
  where sortName = "sort_tfupitlc"

testsForUnifiedPatternInTopLevelGenericContext
    :: MetaOrObject level
    => level
    -> NamePrefix
    -> DeclaredSort level
    -> SortVariablesThatMustBeDeclared level
    -> [KoreSentence]
    -> PatternRestrict
    -> [TestPattern level -> TestData]
testsForUnifiedPatternInTopLevelGenericContext
    x
    (NamePrefix namePrefix)
    (DeclaredSort additionalSort)
    (SortVariablesThatMustBeDeclared sortVariables)
    additionalSentences
    patternRestrict
 =
    [ \testPattern -> TestData
        { testDataDescription = "Pattern in axiom"
        , testDataError =
            Error
                ( "module 'MODULE'"
                : "axiom declaration"
                : testPatternErrorStackStrings testPattern
                )
                defaultErrorMessage
        , testDataDefinition =
            simpleDefinitionFromSentences (ModuleName "MODULE")
                ( axiomSentenceWithSortParameters
                    (testPatternUnifiedPattern testPattern) unifiedSortVariables
                : additionalSentences
                )
        }
    , \testPattern -> TestData
        { testDataDescription = "Pattern in alias definition attributes"
        , testDataError =
            Error
                ( "module 'MODULE'"
                : ("alias '" ++ rawAliasName ++ "' declaration")
                : "attributes"
                : testPatternErrorStackStrings testPattern
                )
                defaultErrorMessage
        , testDataDefinition =
            simpleDefinitionFromSentences
                (ModuleName "MODULE")
                ( asKoreAliasSentence
                    (sentenceAliasWithAttributes
                        aliasName
                        sortVariables
                        additionalSort
                        [ testPatternUnifiedPattern testPattern ]
                    )
                : additionalSentences
                )
        }
    , \testPattern -> TestData
        { testDataDescription = "Pattern in symbol definition attributes"
        , testDataError =
            Error
                ( "module 'MODULE'"
                : ("symbol '" ++ rawSymbolName ++ "' declaration")
                : "attributes"
                : testPatternErrorStackStrings testPattern
                )
                defaultErrorMessage
        , testDataDefinition =
            simpleDefinitionFromSentences
                (ModuleName "MODULE")
                ( asKoreSymbolSentence
                    (sentenceSymbolWithAttributes
                        symbolName
                        sortVariables
                        additionalSort
                        [ testPatternUnifiedPattern testPattern ]
                    )
                : additionalSentences
                )
        }
    , \testPattern -> TestData
        { testDataDescription = "Axiom with attributes"
        , testDataError =
            Error
                ( "module 'MODULE'"
                : "axiom declaration"
                : "attributes"
                : testPatternErrorStackStrings testPattern
                )
                defaultErrorMessage
        , testDataDefinition =
            simpleDefinitionFromSentences
                (ModuleName "MODULE")
                ( axiomSentenceWithAttributes
                    unifiedSortVariables
                    (simpleExistsUnifiedPatternWithType
                        x  variableName1 additionalSort)
                    [ testPatternUnifiedPattern testPattern ]
                : additionalSentences
                )
        }
    ]
    ++ case patternRestrict of
        NeedsSortVariables -> []
        _ ->
            [ \testPattern -> TestData
                { testDataDescription = "Module with attributes"
                , testDataError =
                    Error
                        ( "module 'MODULE'"
                        : "attributes"
                        : testPatternErrorStackStrings testPattern
                        )
                        defaultErrorMessage
                , testDataDefinition =
                    Definition
                        { definitionAttributes = Attributes []
                        , definitionModules =
                            [ Module
                                { moduleName = ModuleName "MODULE"
                                , moduleSentences = additionalSentences
                                , moduleAttributes =
                                    Attributes
                                        [ testPatternUnifiedPattern testPattern ]
                                }
                            ]
                        }
                }
            ]
    ++ case patternRestrict of
        NeedsSortVariables -> []
        NeedsInternalDefinitions -> []
        NeedsSortedParent -> []
        _ ->
            [ \testPattern -> TestData
                { testDataDescription = "Definition with attributes"
                , testDataError =
                    Error
                        ( "attributes"
                        : testPatternErrorStackStrings testPattern
                        )
                        defaultErrorMessage
                , testDataDefinition =
                    Definition
                        { definitionAttributes =
                            Attributes
                                [ testPatternUnifiedPattern testPattern ]
                        , definitionModules =
                            [ Module
                                { moduleName = ModuleName "MODULE"
                                , moduleSentences = additionalSentences
                                , moduleAttributes = Attributes []
                                }
                            ]
                        }
                }
            ]
  where
    unifiedSortVariables = map asUnified sortVariables
    rawAliasName = namePrefix ++ "_alias"
    aliasName = AliasName rawAliasName
    rawSymbolName = namePrefix ++ "_symbol"
    symbolName = SymbolName rawSymbolName
    rawVariableName1 = namePrefix ++ "_var"
    variableName1 = VariableName rawVariableName1

testsForUnifiedPatternInTopLevelObjectContext
    :: MetaOrObject level
    => SortName
    -> SortVariablesThatMustBeDeclared Object
    -> [KoreSentence]
    -> [TestPattern level -> TestData]
testsForUnifiedPatternInTopLevelObjectContext
    (SortName rawSortName)
    (SortVariablesThatMustBeDeclared sortVariables)
    additionalSentences
  =
    [ \testPattern -> TestData
        { testDataDescription = "Pattern in Sort declaration"
        , testDataError =
            Error
                ( "module 'MODULE'"
                : ("sort '" ++ rawSortName ++ "' declaration")
                : "attributes"
                : testPatternErrorStackStrings testPattern
                )
                defaultErrorMessage
        , testDataDefinition =
            simpleDefinitionFromSentences (ModuleName "MODULE")
                ( asSentence SentenceSort
                    { sentenceSortName = Id rawSortName
                    , sentenceSortParameters = sortVariables
                    , sentenceSortAttributes =
                        Attributes [ testPatternUnifiedPattern testPattern ]
                    }
                : additionalSentences
                )
        }
    ]

defaultErrorMessage :: String
defaultErrorMessage = "Replace this with a real error message."


    -- MLPatternType
    -- Application
    -- axiom
    -- attributes -- module and definition
