module Test.Kore.ASTVerifier.DefinitionVerifier.PatternVerifier
    ( test_patternVerifier
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( HasCallStack )

import qualified Data.List as List

import Kore.AST.AstWithLocation
import Kore.AST.Common
import Kore.AST.Kore
import Kore.AST.MetaOrObject
import Kore.AST.Sentence
import Kore.Building.Implicit
import Kore.Building.Patterns as Patterns
import Kore.Error
import Kore.Implicit.ImplicitSorts

import Test.Kore
import Test.Kore.ASTVerifier.DefinitionVerifier as Helpers

data PatternRestrict
    = NeedsInternalDefinitions
    | NeedsSortedParent

data TestPattern level = TestPattern
    { testPatternPattern    :: !(Pattern level Variable CommonKorePattern)
    , testPatternSort       :: !(Sort level)
    , testPatternErrorStack :: !ErrorStack
    }

newtype VariableOfDeclaredSort level = VariableOfDeclaredSort (Variable level)

testPatternErrorStackStrings :: TestPattern level -> [String]
testPatternErrorStackStrings
    TestPattern {testPatternErrorStack = ErrorStack strings}
  =
    strings

testPatternUnifiedPattern
    :: MetaOrObject level => TestPattern level -> CommonKorePattern
testPatternUnifiedPattern
    TestPattern {testPatternPattern = p}
  =
    asKorePattern p

test_patternVerifier :: [TestTree]
test_patternVerifier =
    [ expectSuccess "Simplest definition"
        (simpleDefinitionFromSentences (ModuleName "MODULE") [])
    , successTestsForObjectPattern "Simple object pattern"
        (simpleExistsPattern objectVariable' objectSort)
        (NamePrefix "dummy")
        (TestedPatternSort objectSort)
        (SortVariablesThatMustBeDeclared [])
        (DeclaredSort anotherSort)
        [objectSortSentence, anotherSortSentence]
        NeedsInternalDefinitions
    , successTestsForMetaPattern "Simple meta pattern"
        (simpleExistsPattern metaVariable' metaSort1)
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
            [ "\\exists 'ObjectVariable' (<test data>)"
            , "\\exists 'ObjectVariable' (<test data>)"
            , "sort 'ObjectSort' (<test data>)"
            , "(<test data>)"
            ]
        )
        (ExistsPattern Exists
            { existsSort = anotherSort
            , existsVariable = anotherVariable
            , existsChild =
                asKorePattern
                    (simpleExistsPattern objectVariable' objectSort)
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
            [ "\\exists 'ObjectVariable' (<test data>)"
            , "variable 'ObjectVariable' (<test data>)"
            , "(<test data>, <test data>)"
            ]
        )
        (ExistsPattern Exists
            { existsSort = objectSort
            , existsVariable = objectVariable'
            , existsChild =
                asKorePattern (VariablePattern anotherVariable)
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
        NeedsInternalDefinitions
    , failureTestsForObjectPattern
        "Object pattern - sort variable not defined"
        (ExpectedErrorMessage
            "Sort variable 'ObjectSortVariable' not declared.")
        (ErrorStack
            [ "\\exists 'ObjectVariable' (<test data>)"
            , "\\exists 'ObjectVariable' (<test data>)"
            , "(<test data>)"
            ]
        )
        (ExistsPattern Exists
            { existsSort = objectSort
            , existsVariable = objectVariable'
            , existsChild =
                asKorePattern
                    (simpleExistsPattern
                        objectVariableSortVariable objectSortVariableSort)
            }
        )
        (NamePrefix "dummy")
        (TestedPatternSort objectSort)
        (SortVariablesThatMustBeDeclared [])
        (DeclaredSort anotherSort)
        [objectSortSentence, anotherSortSentence]
        NeedsInternalDefinitions
    , failureTestsForMetaPattern "Meta pattern - sort not defined"
        (ExpectedErrorMessage "Sort '#InvalidMetaSort' not declared.")
        (ErrorStack
            [ "\\exists '#MetaVariable' (<test data>)"
            , "sort '#InvalidMetaSort' (<test data>)"
            , "(<test data>)"
            ]
        )
        (simpleExistsPattern metaVariable' invalidMetaSort)
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
            [ "\\exists 'ObjectVariable' (<test data>)"
            , "variable 'ObjectVariable' (<test data>)"
            , "(<test data>, <test data>)"
            ]
        )
        (simpleExistsPattern objectVariable' anotherObjectSort2)
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
            [ "\\exists '#MetaVariable' (<test data>)"
            , "variable '#MetaVariable' (<test data>)"
            , "(<test data>, <test data>)"
            ]
        )
        (simpleExistsPattern metaVariable' anotherMetaSort2)
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
        (ErrorStack
            [ "symbol or alias 'ObjectSymbol' (<test data>)"
            , "(<test data>)"
            ]
        )
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
        (ErrorStack ["symbol or alias 'ObjectSymbol' (<test data>)"])
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
        (ErrorStack ["symbol or alias 'ObjectSymbol' (<test data>)"])
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
        (ErrorStack ["symbol or alias 'ObjectAlias' (<test data>)"])
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
        (ErrorStack ["symbol or alias '#MetaSymbol' (<test data>)"])
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
        (ErrorStack ["symbol or alias 'ObjectSymbol' (<test data>)"])
        (ApplicationPattern Application
            { applicationSymbolOrAlias = SymbolOrAlias
                { symbolOrAliasConstructor = testId oneSortSymbolRawName
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
        (ErrorStack ["symbol or alias 'ObjectSymbol' (<test data>)"])
        (ApplicationPattern Application
            { applicationSymbolOrAlias = SymbolOrAlias
                { symbolOrAliasConstructor = testId oneSortSymbolRawName
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
        (VariablePattern objectVariable')
        (NamePrefix "dummy")
        (TestedPatternSort objectSort)
        (SortVariablesThatMustBeDeclared [])
        (DeclaredSort anotherSort)
        [ objectSortSentence, anotherSortSentence ]
        NeedsInternalDefinitions
    , successTestsForMetaPattern "Meta pattern - unquantified variable"
        (VariablePattern metaVariable')
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
        (ErrorStack
            [ "<string> (<unknown location>)"
            , "(<test data>, <implicitly defined entity>)"
            ]
        )
        (StringLiteralPattern (StringLiteral "MetaString"))
        (NamePrefix "#dummy")
        (TestedPatternSort (updateAstLocation charMetaSort AstLocationTest))
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
    objectSort :: Sort Object
    objectSort = simpleSort objectSortName
    objectVariableName = VariableName "ObjectVariable"
    objectVariable' = variable objectVariableName objectSort
    objectSortSentence = simpleSortSentence objectSortName
    metaSort1 = updateAstLocation charListMetaSort AstLocationTest
    metaVariable' = variable (VariableName "#MetaVariable") metaSort1
    dummyMetaSort = updateAstLocation patternMetaSort AstLocationTest
    dummyMetaVariable = variable (VariableName "#otherVariable") dummyMetaSort
    anotherSortName = SortName "anotherSort"
    anotherSort :: Sort Object
    anotherSort = simpleSort anotherSortName
    anotherVariable = variable objectVariableName anotherSort
    anotherSortSentence = simpleSortSentence anotherSortName
    anotherMetaSort = updateAstLocation symbolMetaSort AstLocationTest
    anotherObjectSortName2 = SortName "anotherSort2"
    anotherObjectSort2 :: Sort Object
    anotherObjectSort2 = simpleSort anotherObjectSortName2
    anotherObjectSortSentence2 = simpleSortSentence anotherObjectSortName2
    invalidMetaSort :: Sort Meta
    invalidMetaSort = simpleSort (SortName "#InvalidMetaSort")
    anotherMetaSort2 = updateAstLocation variableMetaSort AstLocationTest
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
    objectSortVariableSort :: Sort Object
    objectSortVariableSort = sortVariableSort objectSortVariableName
    objectVariableSortVariable =
        variable objectVariableName objectSortVariableSort
    oneSortSymbolRawName = "ObjectSymbol"
    oneSortSymbolSentence =
        asSentence
            (SentenceSymbol
                { sentenceSymbolSymbol = Symbol
                    { symbolConstructor = testId oneSortSymbolRawName
                    , symbolParams = [objectSortVariable]
                    }
                , sentenceSymbolSorts = [anotherObjectSort2]
                , sentenceSymbolResultSort = objectSort
                , sentenceSymbolAttributes =
                    Attributes []
                }
            :: KoreSentenceSymbol Object)

dummyVariableAndSentences :: NamePrefix -> (Variable Object, [KoreSentence])
dummyVariableAndSentences (NamePrefix namePrefix) =
    (dummyVariable, [simpleSortSentence dummySortName])
  where
    dummySortName = SortName (namePrefix ++ "_OtherSort")
    dummySort' = simpleSort dummySortName
    dummyVariable =
        variable (VariableName (namePrefix ++ "_OtherVariable")) dummySort'


successTestsForObjectPattern
    :: String
    -> Pattern Object Variable CommonKorePattern
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
    -> Pattern Meta Variable CommonKorePattern
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
    :: HasCallStack
    => String
    -> ExpectedErrorMessage
    -> ErrorStack
    -> Pattern Object Variable CommonKorePattern
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
    dummySort' = simpleSort dummySortName
    dummyVariable =
        variable (VariableName (rawNamePrefix ++ "_OtherVariable")) dummySort'
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
    :: HasCallStack
    => String
    -> ExpectedErrorMessage
    -> ErrorStack
    -> Pattern Meta Variable CommonKorePattern
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
    -> Pattern level Variable CommonKorePattern
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
            , existsChild = asKorePattern (VariablePattern anotherVariable)
            }
    anotherVariable =
        Variable
            { variableName = testId (namePrefix ++ "_anotherVar")
            , variableSort = testedSort
            }
    rawSymbolName = namePrefix ++ "_anotherSymbol"
    rawAliasName = namePrefix ++ "_anotherAlias"
    symbolFromSort sort =
        SymbolOrAlias
            { symbolOrAliasConstructor = testId rawSymbolName
            , symbolOrAliasParams = [sort]
            }
    aliasFromSort sort =
        SymbolOrAlias
            { symbolOrAliasConstructor = testId rawAliasName
            , symbolOrAliasParams = [sort]
            }

objectPatternInAllContexts
    :: Pattern Object Variable CommonKorePattern
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
            , existsChild = asKorePattern (VariablePattern anotherVariable)
            }
    anotherVariable =
        Variable
            { variableName = testId (namePrefix ++ "_anotherVar")
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
        constructUnifiedSentence
            SentenceSymbolSentence
            SentenceSymbol
                { sentenceSymbolSymbol = Symbol
                    { symbolConstructor = testId rawSymbolName
                    , symbolParams = [SortVariable (testId rawSortVariableName)]
                    }
                , sentenceSymbolSorts = [symbolAliasSort]
                , sentenceSymbolResultSort = anotherSort
                , sentenceSymbolAttributes =
                    Attributes []
                }
    aliasSentence =
        constructUnifiedSentence
            SentenceAliasSentence
            SentenceAlias
                { sentenceAliasAlias = Alias
                    { aliasConstructor = testId rawAliasName
                    , aliasParams = [SortVariable (testId rawSortVariableName)]
                    }
                , sentenceAliasSorts = [symbolAliasSort]
                , sentenceAliasResultSort = anotherSort
                , sentenceAliasLeftPattern = TopPattern $ Top anotherSort
                , sentenceAliasRightPattern = TopPattern $ Top anotherSort
                , sentenceAliasAttributes =
                    Attributes []
                }

genericPatternInPatterns
    :: MetaOrObject level
    => Pattern level Variable CommonKorePattern
    -> Pattern level Variable CommonKorePattern
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
                , testPatternSort = testedSort
                , testPatternErrorStack = ErrorStack []
                }
            ]
    ++
        [ TestPattern
            { testPatternPattern = ApplicationPattern Application
                { applicationSymbolOrAlias = symbol
                , applicationChildren = [asKorePattern testedPattern]
                }
            , testPatternSort = testedSort
            , testPatternErrorStack =
                ErrorStack
                    [ "symbol or alias '"
                        ++ getId (symbolOrAliasConstructor symbol)
                        ++ "' (<test data>)"
                    ]
            }
        , TestPattern
            { testPatternPattern = ApplicationPattern Application
                { applicationSymbolOrAlias = alias
                , applicationChildren = [asKorePattern testedPattern]
                }
            , testPatternSort = testedSort
            , testPatternErrorStack =
                ErrorStack
                    [ "symbol or alias '"
                        ++ getId (symbolOrAliasConstructor alias)
                        ++ "' (<test data>)"
                    ]
            }
        ]

objectPatternInPatterns
    :: Pattern Object Variable CommonKorePattern
    -> Pattern Object Variable CommonKorePattern
    -> OperandSort Object
    -> [TestPattern Object]
objectPatternInPatterns = patternInUnquantifiedObjectPatterns

patternInQuantifiedPatterns
    :: MetaOrObject level
    => Pattern level Variable CommonKorePattern
    -> Sort level
    -> Variable level
    -> [TestPattern level]
patternInQuantifiedPatterns testedPattern testedSort quantifiedVariable =
    [ TestPattern
        { testPatternPattern = ExistsPattern Exists
            { existsSort = testedSort
            , existsVariable = quantifiedVariable
            , existsChild = asKorePattern testedPattern
            }
        , testPatternSort = testedSort
        , testPatternErrorStack =
            ErrorStack
                [ "\\exists '"
                    ++ getId (variableName quantifiedVariable)
                    ++ "' (<test data>)"
                ]
        }
    , TestPattern
        { testPatternPattern = ForallPattern Forall
            { forallSort = testedSort
            , forallVariable = quantifiedVariable
            , forallChild = asKorePattern testedPattern
            }
        , testPatternSort = testedSort
        , testPatternErrorStack =
            ErrorStack
                [ "\\forall '"
                    ++ getId (variableName quantifiedVariable)
                    ++ "' (<test data>)"
                ]
        }
    ]

patternInUnquantifiedGenericPatterns
    :: MetaOrObject level
    => Pattern level Variable CommonKorePattern
    -> Pattern level Variable CommonKorePattern
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
        , testPatternSort = testedSort
        , testPatternErrorStack = ErrorStack ["\\and (<test data>)"]
        }
    , TestPattern
        { testPatternPattern = AndPattern And
            { andSort = testedSort
            , andFirst = anotherUnifiedPattern
            , andSecond = testedUnifiedPattern
            }
        , testPatternSort = testedSort
        , testPatternErrorStack = ErrorStack ["\\and (<test data>)"]
        }
    , TestPattern
        { testPatternPattern = CeilPattern Ceil
            { ceilOperandSort = testedSort
            , ceilResultSort = resultSort
            , ceilChild = testedUnifiedPattern
            }
        , testPatternSort = resultSort
        , testPatternErrorStack = ErrorStack ["\\ceil (<test data>)"]
        }
    , TestPattern
        { testPatternPattern = EqualsPattern Equals
            { equalsOperandSort = testedSort
            , equalsResultSort = resultSort
            , equalsFirst = testedUnifiedPattern
            , equalsSecond = anotherUnifiedPattern
            }
        , testPatternSort = resultSort
        , testPatternErrorStack = ErrorStack ["\\equals (<test data>)"]
        }
    , TestPattern
        { testPatternPattern = EqualsPattern Equals
            { equalsOperandSort = testedSort
            , equalsResultSort = resultSort
            , equalsFirst = anotherUnifiedPattern
            , equalsSecond = testedUnifiedPattern
            }
        , testPatternSort = resultSort
        , testPatternErrorStack = ErrorStack ["\\equals (<test data>)"]
        }
    , TestPattern
        { testPatternPattern = FloorPattern Floor
            { floorOperandSort = testedSort
            , floorResultSort = resultSort
            , floorChild = testedUnifiedPattern
            }
        , testPatternSort = resultSort
        , testPatternErrorStack = ErrorStack ["\\floor (<test data>)"]
        }
    , TestPattern
        { testPatternPattern = IffPattern Iff
            { iffSort = testedSort
            , iffFirst = testedUnifiedPattern
            , iffSecond = anotherUnifiedPattern
            }
        , testPatternSort = testedSort
        , testPatternErrorStack = ErrorStack ["\\iff (<test data>)"]
        }
    , TestPattern
        { testPatternPattern = IffPattern Iff
            { iffSort = testedSort
            , iffFirst = anotherUnifiedPattern
            , iffSecond = testedUnifiedPattern
            }
        , testPatternSort = testedSort
        , testPatternErrorStack = ErrorStack ["\\iff (<test data>)"]
        }
    , TestPattern
        { testPatternPattern = ImpliesPattern Implies
            { impliesSort = testedSort
            , impliesFirst = testedUnifiedPattern
            , impliesSecond = anotherUnifiedPattern
            }
        , testPatternSort = testedSort
        , testPatternErrorStack = ErrorStack ["\\implies (<test data>)"]
        }
    , TestPattern
        { testPatternPattern = ImpliesPattern Implies
            { impliesSort = testedSort
            , impliesFirst = anotherUnifiedPattern
            , impliesSecond = testedUnifiedPattern
            }
        , testPatternSort = testedSort
        , testPatternErrorStack = ErrorStack ["\\implies (<test data>)"]
        }
    , TestPattern
        { testPatternPattern = InPattern In
            { inOperandSort = testedSort
            , inResultSort = resultSort
            , inContainedChild = testedUnifiedPattern
            , inContainingChild = anotherUnifiedPattern
            }
        , testPatternSort = resultSort
        , testPatternErrorStack = ErrorStack ["\\in (<test data>)"]
        }
    , TestPattern
        { testPatternPattern = InPattern In
            { inOperandSort = testedSort
            , inResultSort = resultSort
            , inContainedChild = anotherUnifiedPattern
            , inContainingChild = testedUnifiedPattern
            }
        , testPatternSort = resultSort
        , testPatternErrorStack = ErrorStack ["\\in (<test data>)"]
        }
    , TestPattern
        { testPatternPattern = NotPattern Not
            { notSort = testedSort
            , notChild = testedUnifiedPattern
            }
        , testPatternSort = testedSort
        , testPatternErrorStack = ErrorStack ["\\not (<test data>)"]
        }
    , TestPattern
        { testPatternPattern = OrPattern Or
            { orSort = testedSort
            , orFirst = testedUnifiedPattern
            , orSecond = anotherUnifiedPattern
            }
        , testPatternSort = testedSort
        , testPatternErrorStack = ErrorStack ["\\or (<test data>)"]
        }
    , TestPattern
        { testPatternPattern = OrPattern Or
            { orSort = testedSort
            , orFirst = anotherUnifiedPattern
            , orSecond = testedUnifiedPattern
            }
        , testPatternSort = testedSort
        , testPatternErrorStack = ErrorStack ["\\or (<test data>)"]
        }
    ]
  where
    anotherUnifiedPattern = asKorePattern anotherPattern
    testedUnifiedPattern = asKorePattern testedPattern

patternInUnquantifiedObjectPatterns
    :: Pattern Object Variable CommonKorePattern
    -> Pattern Object Variable CommonKorePattern
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
        , testPatternSort = testedSort
        , testPatternErrorStack = ErrorStack ["\\next (<test data>)"]
        }
    , TestPattern
        { testPatternPattern = RewritesPattern Rewrites
            { rewritesSort = testedSort
            , rewritesFirst = testedUnifiedPattern
            , rewritesSecond = anotherUnifiedPattern
            }
        , testPatternSort = testedSort
        , testPatternErrorStack = ErrorStack ["\\rewrites (<test data>)"]
        }
    , TestPattern
        { testPatternPattern = RewritesPattern Rewrites
            { rewritesSort = testedSort
            , rewritesFirst = anotherUnifiedPattern
            , rewritesSecond = testedUnifiedPattern
            }
        , testPatternSort = testedSort
        , testPatternErrorStack = ErrorStack ["\\rewrites (<test data>)"]
        }

    ]
  where
    anotherUnifiedPattern = asKorePattern anotherPattern
    testedUnifiedPattern = asKorePattern testedPattern

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
    _
  =
    testsForUnifiedPatternInTopLevelGenericContext
        x
        namePrefix
        additionalSort
        sortVariables

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
    _
    (NamePrefix _)
    (DeclaredSort _)
    (SortVariablesThatMustBeDeclared sortVariables)
    additionalSentences
    patternRestrict
  =
    let
        axiomPattern testPattern = TestData
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
                        (testPatternUnifiedPattern testPattern)
                        unifiedSortVariables
                    : additionalSentences
                    )
            }
    in case patternRestrict of
        NeedsInternalDefinitions -> [axiomPattern]
        NeedsSortedParent        -> [axiomPattern]

  where
    unifiedSortVariables = map asUnified sortVariables

defaultErrorMessage :: String
defaultErrorMessage = "Replace this with a real error message."


    -- MLPatternType
    -- Application
    -- axiom
    -- attributes -- module and definition
