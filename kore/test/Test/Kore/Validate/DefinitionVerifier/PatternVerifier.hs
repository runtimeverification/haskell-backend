{-# OPTIONS_GHC -Wno-x-partial #-} -- no head/tail warnings

module Test.Kore.Validate.DefinitionVerifier.PatternVerifier (
    test_patternVerifier,
    test_verifyBinder,
) where

import Data.List qualified as List
import Data.Text qualified as Text
import Kore.Attribute.Hook qualified as Attribute.Hook
import Kore.Attribute.Simplification (
    simplificationAttribute,
 )
import Kore.Attribute.Sort.HasDomainValues qualified as Attribute.HasDomainValues
import Kore.Error
import Kore.IndexedModule.Error (
    noSort,
 )
import Kore.IndexedModule.IndexedModule (
    IndexedModule (..),
 )
import Kore.Internal.TermLike qualified as Internal
import Kore.Syntax
import Kore.Syntax.Definition
import Kore.Validate.Error (
    sortNeedsDomainValueAttributeMessage,
 )
import Kore.Validate.PatternVerifier as PatternVerifier
import Prelude.Kore
import Test.Kore
import Test.Kore.Builtin.Builtin qualified as Builtin
import Test.Kore.Builtin.Definition qualified as Builtin
import Test.Kore.Builtin.External
import Test.Kore.Validate.DefinitionVerifier as Helpers
import Test.Tasty (
    TestTree,
 )
import Test.Tasty.HUnit

data PatternRestrict
    = NeedsInternalDefinitions
    | NeedsSortedParent

data TestPattern = TestPattern
    { testPatternPattern :: !(PatternF VariableName ParsedPattern)
    , testPatternSort :: !Sort
    , testPatternErrorStack :: !ErrorStack
    }

newtype VariableOfDeclaredSort
    = VariableOfDeclaredSort (ElementVariable VariableName)

testPatternErrorStackStrings :: TestPattern -> [String]
testPatternErrorStackStrings
    TestPattern{testPatternErrorStack = ErrorStack strings} =
        strings

testPatternUnverifiedPattern :: TestPattern -> ParsedPattern
testPatternUnverifiedPattern TestPattern{testPatternPattern} =
    embedParsedPattern testPatternPattern

test_patternVerifier :: [TestTree]
test_patternVerifier =
    [ expectSuccess
        "Simplest definition"
        (simpleDefinitionFromSentences (ModuleName "MODULE") [])
    , successTestsForObjectPattern
        "Simple object pattern"
        (simpleExistsPattern objectVariable' objectSort)
        (NamePrefix "dummy")
        (TestedPatternSort objectSort)
        (SortVariablesThatMustBeDeclared [])
        (DeclaredSort anotherSort)
        [objectSortSentence, anotherSortSentence]
        NeedsInternalDefinitions
    , failureTestsForObjectPattern
        "Object pattern - sort not defined"
        (ExpectedErrorMessage $ noSort "ObjectSort")
        ( ErrorStack
            [ "\\exists 'ObjectVariable' (<test data>)"
            , "\\exists 'ObjectVariable' (<test data>)"
            , "sort 'ObjectSort' (<test data>)"
            , "(<test data>)"
            ]
        )
        ( ExistsF
            Exists
                { existsSort = anotherSort
                , existsVariable = anotherVariable
                , existsChild =
                    embedParsedPattern $ simpleExistsPattern objectVariable' objectSort
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
        ( ErrorStack
            [ "\\exists 'ObjectVariable' (<test data>)"
            , "element variable 'ObjectVariable' (<test data>)"
            , "(<test data>, <test data>)"
            ]
        )
        ( ExistsF
            Exists
                { existsSort = objectSort
                , existsVariable = objectVariable'
                , existsChild =
                    externalize $ Internal.mkElemVar anotherVariable
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
        ( simpleExistsPattern
            objectVariableSortVariable
            objectSortVariableSort
        )
        (NamePrefix "dummy")
        (TestedPatternSort objectSortVariableSort)
        (SortVariablesThatMustBeDeclared [objectSortVariable])
        (DeclaredSort anotherSort)
        [anotherSortSentence]
        NeedsInternalDefinitions
    , failureTestsForObjectPattern
        "Mu pattern - different variable sort"
        (ExpectedErrorMessage "The declared sort is different.")
        ( ErrorStack
            [ "\\mu (<test data>)"
            , "set variable '@ObjectVariable' (<test data>)"
            , "(<test data>, <test data>)"
            ]
        )
        ( MuF
            Mu
                { muVariable = objectSetVariable'
                , muChild =
                    externalize $
                        Internal.mkSetVar anotherSetVariable
                }
        )
        (NamePrefix "dummy")
        (TestedPatternSort objectSort)
        (SortVariablesThatMustBeDeclared [])
        (DeclaredSort anotherSort)
        [objectSortSentence, anotherSortSentence]
        NeedsInternalDefinitions
    , successTestsForObjectPattern
        "Mu pattern - sort variable defined"
        (simpleMuPattern objectSetVariableSortVariable)
        (NamePrefix "dummy")
        (TestedPatternSort objectSortVariableSort)
        (SortVariablesThatMustBeDeclared [objectSortVariable])
        (DeclaredSort anotherSort)
        [anotherSortSentence]
        NeedsInternalDefinitions
    , failureTestsForObjectPattern
        "Nu pattern - different variable sort"
        (ExpectedErrorMessage "The declared sort is different.")
        ( ErrorStack
            [ "\\nu (<test data>)"
            , "set variable '@ObjectVariable' (<test data>)"
            , "(<test data>, <test data>)"
            ]
        )
        ( NuF
            Nu
                { nuVariable = objectSetVariable'
                , nuChild =
                    externalize $
                        Internal.mkSetVar anotherSetVariable
                }
        )
        (NamePrefix "dummy")
        (TestedPatternSort objectSort)
        (SortVariablesThatMustBeDeclared [])
        (DeclaredSort anotherSort)
        [objectSortSentence, anotherSortSentence]
        NeedsInternalDefinitions
    , successTestsForObjectPattern
        "Nu pattern - sort variable defined"
        (simpleNuPattern objectSetVariableSortVariable)
        (NamePrefix "dummy")
        (TestedPatternSort objectSortVariableSort)
        (SortVariablesThatMustBeDeclared [objectSortVariable])
        (DeclaredSort anotherSort)
        [anotherSortSentence]
        NeedsInternalDefinitions
    , failureTestsForObjectPattern
        "Object pattern - sort variable not defined"
        ( ExpectedErrorMessage
            "Sort variable ObjectSortVariable not declared."
        )
        ( ErrorStack
            [ "\\exists 'ObjectVariable' (<test data>)"
            , "\\exists 'ObjectVariable' (<test data>)"
            , "(<test data>)"
            ]
        )
        ( ExistsF
            Exists
                { existsSort = objectSort
                , existsVariable = objectVariable'
                , existsChild =
                    embedParsedPattern $
                        simpleExistsPattern
                            objectVariableSortVariable
                            objectSortVariableSort
                }
        )
        (NamePrefix "dummy")
        (TestedPatternSort objectSort)
        (SortVariablesThatMustBeDeclared [])
        (DeclaredSort anotherSort)
        [objectSortSentence, anotherSortSentence]
        NeedsInternalDefinitions
    , failureTestsForObjectPattern
        "Object pattern - sort not matched"
        ( ExpectedErrorMessage
            "Expecting sort anotherSort2{} but got ObjectSort{}."
        )
        ( ErrorStack
            [ "\\exists 'ObjectVariable' (<test data>)"
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
    , successTestsForObjectPattern
        "Application pattern - symbol"
        ( applicationPatternWithChildren
            objectSymbolName
            [simpleExistsParsedPattern objectVariableName anotherObjectSort2]
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
    , successTestsForObjectPattern
        "Application pattern - alias"
        ( applicationPatternWithChildren
            objectAliasNameAsSymbol
            [ variableParsedPattern
                objectVariableName
                anotherObjectSort2
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
    , failureTestsForObjectPattern
        "Application pattern - symbol not declared"
        (ExpectedErrorMessage "Head 'ObjectSymbol' not defined.")
        (ErrorStack ["symbol or alias 'ObjectSymbol' (<test data>)"])
        ( applicationPatternWithChildren
            objectSymbolName
            [ simpleExistsParsedPattern
                objectVariableName
                anotherObjectSort2
            ]
        )
        (NamePrefix "dummy")
        (TestedPatternSort objectSort)
        (SortVariablesThatMustBeDeclared [])
        (DeclaredSort anotherSort)
        [ objectSortSentence
        , anotherSortSentence
        , anotherObjectSortSentence2
        -- , objectSymbolSentence
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
    , failureTestsForObjectPattern
        "Object pattern - too many arguments"
        (ExpectedErrorMessage "Expected 1 operands, but got 2.")
        (ErrorStack ["symbol or alias 'ObjectSymbol' (<test data>)"])
        ( applicationPatternWithChildren
            objectSymbolName
            [ simpleExistsParsedPattern
                objectVariableName
                anotherObjectSort2
            , simpleExistsParsedPattern
                objectVariableName
                anotherObjectSort2
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
        ( applicationPatternWithChildren
            objectAliasNameAsSymbol
            [ variableParsedPattern
                objectVariableName
                anotherObjectSort2
            , variableParsedPattern
                objectVariableName
                anotherObjectSort2
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
    , failureTestsForObjectPattern
        "Application pattern - too few sorts"
        ( ExpectedErrorMessage
            "Application uses less sorts than the declaration."
        )
        (ErrorStack ["symbol or alias 'ObjectSymbol' (<test data>)"])
        ( ApplicationF
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = testId oneSortSymbolRawName
                        , symbolOrAliasParams = []
                        }
                , applicationChildren =
                    [ simpleExistsParsedPattern
                        objectVariableName
                        anotherObjectSort2
                    ]
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
    , failureTestsForObjectPattern
        "Application pattern - too many sorts"
        ( ExpectedErrorMessage
            "Application uses more sorts than the declaration."
        )
        (ErrorStack ["symbol or alias 'ObjectSymbol' (<test data>)"])
        ( ApplicationF
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = testId oneSortSymbolRawName
                        , symbolOrAliasParams = [objectSort, objectSort]
                        }
                , applicationChildren =
                    [ simpleExistsParsedPattern
                        objectVariableName
                        anotherObjectSort2
                    ]
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
    , successTestsForObjectPattern
        "Object pattern - unquantified variable"
        (VariableF $ Const $ inject objectVariable')
        (NamePrefix "dummy")
        (TestedPatternSort objectSort)
        (SortVariablesThatMustBeDeclared [])
        (DeclaredSort anotherSort)
        [objectSortSentence, anotherSortSentence]
        NeedsInternalDefinitions
    , successTestsForObjectPattern
        "Bottom pattern"
        (BottomF Bottom{bottomSort = objectSort})
        (NamePrefix "dummy")
        (TestedPatternSort objectSort)
        (SortVariablesThatMustBeDeclared [])
        (DeclaredSort anotherSort)
        [ objectSortSentence
        , anotherSortSentence
        ]
        NeedsInternalDefinitions
    , successTestsForObjectPattern
        "Top pattern"
        (TopF Top{topSort = objectSort})
        (NamePrefix "dummy")
        (TestedPatternSort objectSort)
        (SortVariablesThatMustBeDeclared [])
        (DeclaredSort anotherSort)
        [ objectSortSentence
        , anotherSortSentence
        ]
        NeedsInternalDefinitions
    , failureTestsForObjectPattern
        "Domain value - INT.Int"
        ( ExpectedErrorMessage
            "<string literal>:1:1:\n\
            \  |\n\
            \1 | abcd\n\
            \  | ^\n\
            \unexpected 'a'\n\
            \expecting '+', '-', or integer\n"
        )
        ( ErrorStack
            [ "\\dv (<test data>)"
            , "Verifying builtin sort 'INT.Int'"
            , "While parsing domain value"
            ]
        )
        ( DomainValueF
            DomainValue
                { domainValueSort = intSort
                , domainValueChild =
                    externalize $
                        Internal.mkStringLiteral "abcd" -- Not a decimal integer
                }
        )
        (NamePrefix "dummy")
        (TestedPatternSort intSort)
        (SortVariablesThatMustBeDeclared [])
        (DeclaredSort intSort)
        [asSentence intSortSentence]
        NeedsInternalDefinitions
    , successTestsForObjectPattern
        "Domain value - INT.Int - Negative"
        ( DomainValueF
            DomainValue
                { domainValueSort = intSort
                , domainValueChild =
                    externalize $
                        Internal.mkStringLiteral "-256"
                }
        )
        (NamePrefix "dummy")
        (TestedPatternSort intSort)
        (SortVariablesThatMustBeDeclared [])
        (DeclaredSort intSort)
        [asSentence intSortSentence]
        NeedsInternalDefinitions
    , successTestsForObjectPattern
        "Domain value - INT.Int - Positive (unsigned)"
        ( DomainValueF
            DomainValue
                { domainValueSort = intSort
                , domainValueChild =
                    externalize $
                        Internal.mkStringLiteral "1024"
                }
        )
        (NamePrefix "dummy")
        (TestedPatternSort intSort)
        (SortVariablesThatMustBeDeclared [])
        (DeclaredSort intSort)
        [asSentence intSortSentence]
        NeedsInternalDefinitions
    , successTestsForObjectPattern
        "Domain value - INT.Int - Positive (signed)"
        ( DomainValueF
            DomainValue
                { domainValueSort = intSort
                , domainValueChild =
                    externalize $
                        Internal.mkStringLiteral "+128"
                }
        )
        (NamePrefix "dummy")
        (TestedPatternSort intSort)
        (SortVariablesThatMustBeDeclared [])
        (DeclaredSort intSort)
        [asSentence intSortSentence]
        NeedsInternalDefinitions
    , failureTestsForObjectPattern
        "Domain value - BOOL.Bool"
        ( ExpectedErrorMessage
            "<string literal>:1:1:\n\
            \  |\n\
            \1 | untrue\n\
            \  | ^^^^^\n\
            \unexpected \"untru\"\n\
            \expecting \"false\" or \"true\"\n"
        )
        ( ErrorStack
            [ "\\dv (<test data>)"
            , "Verifying builtin sort 'BOOL.Bool'"
            , "While parsing domain value"
            ]
        )
        ( DomainValueF
            DomainValue
                { domainValueSort = boolSort
                , domainValueChild =
                    externalize $
                        Internal.mkStringLiteral "untrue" -- Not a BOOL.Bool
                }
        )
        (NamePrefix "dummy")
        (TestedPatternSort boolSort)
        (SortVariablesThatMustBeDeclared [])
        (DeclaredSort boolSort)
        [asSentence boolSortSentence]
        NeedsInternalDefinitions
    , successTestsForObjectPattern
        "Domain value - BOOL.Bool - true"
        ( DomainValueF
            DomainValue
                { domainValueSort = boolSort
                , domainValueChild =
                    externalize $
                        Internal.mkStringLiteral "true"
                }
        )
        (NamePrefix "dummy")
        (TestedPatternSort boolSort)
        (SortVariablesThatMustBeDeclared [])
        (DeclaredSort boolSort)
        [asSentence boolSortSentence]
        NeedsInternalDefinitions
    , successTestsForObjectPattern
        "Domain value - BOOL.Bool - false"
        ( DomainValueF
            DomainValue
                { domainValueSort = boolSort
                , domainValueChild =
                    externalize $
                        Internal.mkStringLiteral "false"
                }
        )
        (NamePrefix "dummy")
        (TestedPatternSort boolSort)
        (SortVariablesThatMustBeDeclared [])
        (DeclaredSort boolSort)
        [asSentence boolSortSentence]
        NeedsInternalDefinitions
    , failureTestsForObjectPattern
        "Domain value - sort without DVs"
        ( ExpectedErrorMessage
            (Text.unpack sortNeedsDomainValueAttributeMessage)
        )
        ( ErrorStack
            [ "\\dv (<test data>)"
            , "(<test data>)"
            ]
        )
        ( DomainValueF
            DomainValue
                { domainValueSort = intSort
                , domainValueChild =
                    externalize $
                        Internal.mkStringLiteral "1" -- Not a decimal integer
                }
        )
        (NamePrefix "dummy")
        (TestedPatternSort intSort)
        (SortVariablesThatMustBeDeclared [])
        (DeclaredSort intSort)
        [asSentence intSortSentenceWithoutDv]
        NeedsInternalDefinitions
    ]
  where
    objectSortName = SortName "ObjectSort"
    objectSort :: Sort
    objectSort = simpleSort objectSortName
    objectVariableName = "ObjectVariable"
    objectVariable' = variable objectVariableName objectSort
    objectSetVariable' = setVariable objectVariableName objectSort
    objectSortSentence = simpleSortSentence objectSortName
    anotherSortName = SortName "anotherSort"
    anotherSort :: Sort
    anotherSort = simpleSort anotherSortName
    anotherVariable = variable objectVariableName anotherSort
    anotherSetVariable = setVariable objectVariableName anotherSort
    anotherSortSentence = simpleSortSentence anotherSortName
    anotherObjectSortName2 = SortName "anotherSort2"
    anotherObjectSort2 :: Sort
    anotherObjectSort2 = simpleSort anotherObjectSortName2
    anotherObjectSortSentence2 = simpleSortSentence anotherObjectSortName2
    objectSymbolName = SymbolName "ObjectSymbol"
    objectSymbolSentence =
        objectSymbolSentenceWithArguments
            objectSymbolName
            objectSort
            [anotherObjectSort2]
    objectAliasName = AliasName "ObjectAlias"
    objectAliasNameAsSymbol = SymbolName "ObjectAlias"
    objectAliasSentence =
        objectAliasSentenceWithArguments
            objectAliasName
            objectSort
            [inject $ mkElementVariable (testId "x") anotherObjectSort2]
    objectSortVariable = sortVariable "ObjectSortVariable"
    objectSortVariableSort :: Sort
    objectSortVariableSort = sortVariableSort "ObjectSortVariable"
    objectVariableSortVariable =
        variable objectVariableName objectSortVariableSort
    objectSetVariableSortVariable =
        setVariable objectVariableName objectSortVariableSort
    oneSortSymbolRawName = "ObjectSymbol"
    oneSortSymbolSentence :: ParsedSentence
    oneSortSymbolSentence =
        asSentence
            SentenceSymbol
                { sentenceSymbolSymbol =
                    Symbol
                        { symbolConstructor = testId oneSortSymbolRawName
                        , symbolParams = [objectSortVariable]
                        }
                , sentenceSymbolSorts = [anotherObjectSort2]
                , sentenceSymbolResultSort = objectSort
                , sentenceSymbolAttributes = Attributes []
                }
    intSortName = SortName "Int"
    intSort :: Sort
    intSort = simpleSort intSortName
    intSortSentence :: ParsedSentenceHook
    intSortSentence =
        SentenceHookedSort
            SentenceSort
                { sentenceSortName = testId name
                , sentenceSortParameters = []
                , sentenceSortAttributes =
                    Attributes
                        [ Attribute.Hook.hookAttribute "INT.Int"
                        , Attribute.HasDomainValues.hasDomainValuesAttribute
                        ]
                }
      where
        SortName name = intSortName
    intSortSentenceWithoutDv =
        SentenceHookedSort
            SentenceSort
                { sentenceSortName = testId name
                , sentenceSortParameters = []
                , sentenceSortAttributes =
                    Attributes [Attribute.Hook.hookAttribute "INT.Int"]
                }
      where
        SortName name = intSortName
    boolSortName = SortName "Int"
    boolSort :: Sort
    boolSort = simpleSort boolSortName
    boolSortSentence :: ParsedSentenceHook
    boolSortSentence =
        SentenceHookedSort
            SentenceSort
                { sentenceSortName = testId name
                , sentenceSortParameters = []
                , sentenceSortAttributes =
                    Attributes
                        [ Attribute.Hook.hookAttribute "BOOL.Bool"
                        , Attribute.HasDomainValues.hasDomainValuesAttribute
                        ]
                }
      where
        SortName name = boolSortName

test_verifyBinder :: [TestTree]
test_verifyBinder =
    [ testVerifyExists
    , testVerifyForall
    ]
  where
    context = PatternVerifier.verifiedModuleContext $ indexedModuleSyntax Builtin.verifiedModule
    testVerifyBinder name expect =
        testCase name $ do
            let original = externalize expect
                verifier = verifyStandalonePattern Nothing original
                actual = assertRight $ runPatternVerifier context verifier
            assertEqual "" expect actual
            on (assertEqual "") Internal.extractAttributes expect actual
    testVerifyExists =
        testVerifyBinder "verifyExists" expect
      where
        x = Internal.mkElementVariable "x" Builtin.intSort
        expect = Internal.mkExists x (Internal.mkElemVar x)
    testVerifyForall =
        testVerifyBinder "verifyForall" expect
      where
        x = Internal.mkElementVariable "x" Builtin.intSort
        expect = Internal.mkForall x (Internal.mkElemVar x)

dummyVariableAndSentences ::
    NamePrefix -> (ElementVariable VariableName, [ParsedSentence])
dummyVariableAndSentences (NamePrefix namePrefix) =
    (dummyVariable, [simpleSortSentence dummySortName])
  where
    dummySortName = SortName (namePrefix <> "_OtherSort")
    dummySort' = simpleSort dummySortName
    dummyVariable = variable (namePrefix <> "_OtherVariable") dummySort'

successTestsForObjectPattern ::
    HasCallStack =>
    String ->
    PatternF VariableName ParsedPattern ->
    NamePrefix ->
    TestedPatternSort ->
    SortVariablesThatMustBeDeclared ->
    DeclaredSort ->
    [ParsedSentence] ->
    PatternRestrict ->
    TestTree
successTestsForObjectPattern
    description
    testedPattern
    namePrefix
    testedSort
    sortVariables
    anotherSort
    sentences
    patternRestrict =
        successTestDataGroup description testData
      where
        (dummyVariable, dummySortSentences) =
            dummyVariableAndSentences namePrefix
        testData =
            genericPatternInAllContexts
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

failureTestsForObjectPattern ::
    HasCallStack =>
    String ->
    ExpectedErrorMessage ->
    ErrorStack ->
    PatternF VariableName ParsedPattern ->
    NamePrefix ->
    TestedPatternSort ->
    SortVariablesThatMustBeDeclared ->
    DeclaredSort ->
    [ParsedSentence] ->
    PatternRestrict ->
    TestTree
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
    patternRestrict =
        failureTestDataGroup
            description
            errorMessage
            errorStackSuffix
            testData
      where
        dummySortName = SortName (rawNamePrefix <> "_OtherSort")
        dummySort' = simpleSort dummySortName
        dummyVariable =
            variable (rawNamePrefix <> "_OtherVariable") dummySort'
        dummySortSentence = simpleSortSentence dummySortName
        testData =
            genericPatternInAllContexts
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

genericPatternInAllContexts ::
    PatternF VariableName ParsedPattern ->
    NamePrefix ->
    TestedPatternSort ->
    SortVariablesThatMustBeDeclared ->
    SortVariablesThatMustBeDeclared ->
    DeclaredSort ->
    VariableOfDeclaredSort ->
    [ParsedSentence] ->
    PatternRestrict ->
    [TestData]
genericPatternInAllContexts
    testedPattern
    (NamePrefix namePrefix)
    (TestedPatternSort testedSort)
    sortVariables
    objectSortVariables
    (DeclaredSort anotherSort)
    dummyVariable
    sentences
    patternRestrict =
        patternsInAllContexts
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
            ExistsF
                Exists
                    { existsSort = testedSort
                    , existsVariable = anotherVariable
                    , existsChild =
                        externalize $ Internal.mkElemVar anotherVariable
                    }
        anotherVariable =
            mkElementVariable (testId (namePrefix <> "_anotherVar")) testedSort
        rawSymbolName = namePrefix <> "_anotherSymbol"
        rawAliasName = namePrefix <> "_anotherAlias"
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

objectPatternInAllContexts ::
    PatternF VariableName ParsedPattern ->
    NamePrefix ->
    TestedPatternSort ->
    SortVariablesThatMustBeDeclared ->
    DeclaredSort ->
    [ParsedSentence] ->
    PatternRestrict ->
    [TestData]
objectPatternInAllContexts
    testedPattern
    (NamePrefix namePrefix)
    (TestedPatternSort testedSort)
    sortVariables
    (DeclaredSort anotherSort) =
        patternsInAllContexts
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
            ExistsF
                Exists
                    { existsSort = testedSort
                    , existsVariable = anotherVariable
                    , existsChild =
                        externalize $
                            Internal.mkElemVar anotherVariable
                    }
        anotherVariable =
            mkElementVariable (testId (namePrefix <> "_anotherVar")) testedSort

patternsInAllContexts ::
    [TestPattern] ->
    NamePrefix ->
    SortVariablesThatMustBeDeclared ->
    SortVariablesThatMustBeDeclared ->
    DeclaredSort ->
    [ParsedSentence] ->
    PatternRestrict ->
    [TestData]
patternsInAllContexts
    patterns
    (NamePrefix namePrefix)
    sortVariables
    objectSortVariables
    (DeclaredSort anotherSort)
    sentences
    patternRestrict =
        map (\context -> context (List.head patterns)) contextExpansion
            ++ map (List.head contextExpansion) patterns
      where
        contextExpansion =
            testsForUnifiedPatternInTopLevelContext
                (NamePrefix (namePrefix <> "_piac"))
                (DeclaredSort anotherSort)
                sortVariables
                objectSortVariables
                ( symbolSentence
                    : aliasSentence
                    : sentences
                )
                patternRestrict
        rawSymbolName = namePrefix <> "_anotherSymbol"
        rawAliasName = namePrefix <> "_anotherAlias"
        rawSortVariableName = namePrefix <> "_sortVariable"
        symbolAliasSort = sortVariableSort rawSortVariableName
        symbolSentence =
            SentenceSymbolSentence
                SentenceSymbol
                    { sentenceSymbolSymbol =
                        Symbol
                            { symbolConstructor = testId rawSymbolName
                            , symbolParams = [SortVariable (testId rawSortVariableName)]
                            }
                    , sentenceSymbolSorts = [symbolAliasSort]
                    , sentenceSymbolResultSort = anotherSort
                    , sentenceSymbolAttributes = Attributes []
                    }
        aliasSentence :: ParsedSentence
        aliasSentence =
            let aliasConstructor = testId rawAliasName
                aliasParams = [SortVariable (testId rawSortVariableName)]
             in SentenceAliasSentence
                    SentenceAlias
                        { sentenceAliasAlias = Alias{aliasConstructor, aliasParams}
                        , sentenceAliasSorts = [symbolAliasSort]
                        , sentenceAliasResultSort = anotherSort
                        , sentenceAliasLeftPattern =
                            Application
                                { applicationSymbolOrAlias =
                                    SymbolOrAlias
                                        { symbolOrAliasConstructor = aliasConstructor
                                        , symbolOrAliasParams =
                                            SortVariableSort <$> aliasParams
                                        }
                                , applicationChildren =
                                    [inject $ mkSetVariable (testId "x") symbolAliasSort]
                                }
                        , sentenceAliasRightPattern =
                            externalize $ Internal.mkTop anotherSort
                        , sentenceAliasAttributes = Attributes []
                        }

genericPatternInPatterns ::
    PatternF VariableName ParsedPattern ->
    PatternF VariableName ParsedPattern ->
    OperandSort ->
    Helpers.ResultSort ->
    VariableOfDeclaredSort ->
    SymbolOrAlias ->
    SymbolOrAlias ->
    PatternRestrict ->
    [TestPattern]
genericPatternInPatterns
    testedPattern
    anotherPattern
    sort@(OperandSort testedSort)
    resultSort
    (VariableOfDeclaredSort dummyVariable)
    symbol
    alias
    patternRestrict =
        patternInQuantifiedPatterns testedPattern testedSort dummyVariable
            ++ patternInUnquantifiedGenericPatterns
                testedPattern
                anotherPattern
                sort
                resultSort
            ++ case patternRestrict of
                NeedsSortedParent -> []
                _ ->
                    [ TestPattern
                        { testPatternPattern = testedPattern
                        , testPatternSort = testedSort
                        , testPatternErrorStack = ErrorStack []
                        }
                    ]
            ++ [ TestPattern
                    { testPatternPattern =
                        ApplicationF
                            Application
                                { applicationSymbolOrAlias = symbol
                                , applicationChildren = [embedParsedPattern testedPattern]
                                }
                    , testPatternSort = testedSort
                    , testPatternErrorStack =
                        ErrorStack
                            [ "symbol or alias '"
                                ++ getIdForError (symbolOrAliasConstructor symbol)
                                ++ "' (<test data>)"
                            ]
                    }
               , TestPattern
                    { testPatternPattern =
                        ApplicationF
                            Application
                                { applicationSymbolOrAlias = alias
                                , applicationChildren = [embedParsedPattern testedPattern]
                                }
                    , testPatternSort = testedSort
                    , testPatternErrorStack =
                        ErrorStack
                            [ "symbol or alias '"
                                ++ getIdForError (symbolOrAliasConstructor alias)
                                ++ "' (<test data>)"
                            ]
                    }
               ]

objectPatternInPatterns ::
    PatternF VariableName ParsedPattern ->
    PatternF VariableName ParsedPattern ->
    OperandSort ->
    [TestPattern]
objectPatternInPatterns = patternInUnquantifiedObjectPatterns

patternInQuantifiedPatterns ::
    PatternF VariableName ParsedPattern ->
    Sort ->
    ElementVariable VariableName ->
    [TestPattern]
patternInQuantifiedPatterns testedPattern testedSort quantifiedVariable =
    [ TestPattern
        { testPatternPattern =
            ExistsF
                Exists
                    { existsSort = testedSort
                    , existsVariable = quantifiedVariable
                    , existsChild = testedKorePattern
                    }
        , testPatternSort = testedSort
        , testPatternErrorStack =
            ErrorStack
                [ "\\exists '"
                    ++ getIdForError
                        ( base . unElementVariableName . variableName $
                            quantifiedVariable
                        )
                    ++ "' (<test data>)"
                ]
        }
    , TestPattern
        { testPatternPattern =
            ForallF
                Forall
                    { forallSort = testedSort
                    , forallVariable = quantifiedVariable
                    , forallChild = testedKorePattern
                    }
        , testPatternSort = testedSort
        , testPatternErrorStack =
            ErrorStack
                [ "\\forall '"
                    ++ getIdForError
                        ( base . unElementVariableName . variableName $
                            quantifiedVariable
                        )
                    ++ "' (<test data>)"
                ]
        }
    ]
  where
    testedKorePattern = embedParsedPattern testedPattern

patternInUnquantifiedGenericPatterns ::
    PatternF VariableName ParsedPattern ->
    PatternF VariableName ParsedPattern ->
    OperandSort ->
    Helpers.ResultSort ->
    [TestPattern]
patternInUnquantifiedGenericPatterns
    testedPattern
    anotherPattern
    (OperandSort testedSort)
    (Helpers.ResultSort resultSort) =
        [ TestPattern
            { testPatternPattern =
                AndF
                    And
                        { andSort = testedSort
                        , andChildren = [testedUnifiedPattern, anotherUnifiedPattern]
                        }
            , testPatternSort = testedSort
            , testPatternErrorStack = ErrorStack ["\\and (<test data>)"]
            }
        , TestPattern
            { testPatternPattern =
                AndF
                    And
                        { andSort = testedSort
                        , andChildren = [anotherUnifiedPattern, testedUnifiedPattern]
                        }
            , testPatternSort = testedSort
            , testPatternErrorStack = ErrorStack ["\\and (<test data>)"]
            }
        , TestPattern
            { testPatternPattern =
                CeilF
                    Ceil
                        { ceilOperandSort = testedSort
                        , ceilResultSort = resultSort
                        , ceilChild = testedUnifiedPattern
                        }
            , testPatternSort = resultSort
            , testPatternErrorStack = ErrorStack ["\\ceil (<test data>)"]
            }
        , TestPattern
            { testPatternPattern =
                EqualsF
                    Equals
                        { equalsOperandSort = testedSort
                        , equalsResultSort = resultSort
                        , equalsFirst = testedUnifiedPattern
                        , equalsSecond = anotherUnifiedPattern
                        }
            , testPatternSort = resultSort
            , testPatternErrorStack = ErrorStack ["\\equals (<test data>)"]
            }
        , TestPattern
            { testPatternPattern =
                EqualsF
                    Equals
                        { equalsOperandSort = testedSort
                        , equalsResultSort = resultSort
                        , equalsFirst = anotherUnifiedPattern
                        , equalsSecond = testedUnifiedPattern
                        }
            , testPatternSort = resultSort
            , testPatternErrorStack = ErrorStack ["\\equals (<test data>)"]
            }
        , TestPattern
            { testPatternPattern =
                FloorF
                    Floor
                        { floorOperandSort = testedSort
                        , floorResultSort = resultSort
                        , floorChild = testedUnifiedPattern
                        }
            , testPatternSort = resultSort
            , testPatternErrorStack = ErrorStack ["\\floor (<test data>)"]
            }
        , TestPattern
            { testPatternPattern =
                IffF
                    Iff
                        { iffSort = testedSort
                        , iffFirst = testedUnifiedPattern
                        , iffSecond = anotherUnifiedPattern
                        }
            , testPatternSort = testedSort
            , testPatternErrorStack = ErrorStack ["\\iff (<test data>)"]
            }
        , TestPattern
            { testPatternPattern =
                IffF
                    Iff
                        { iffSort = testedSort
                        , iffFirst = anotherUnifiedPattern
                        , iffSecond = testedUnifiedPattern
                        }
            , testPatternSort = testedSort
            , testPatternErrorStack = ErrorStack ["\\iff (<test data>)"]
            }
        , TestPattern
            { testPatternPattern =
                ImpliesF
                    Implies
                        { impliesSort = testedSort
                        , impliesFirst = testedUnifiedPattern
                        , impliesSecond = anotherUnifiedPattern
                        }
            , testPatternSort = testedSort
            , testPatternErrorStack = ErrorStack ["\\implies (<test data>)"]
            }
        , TestPattern
            { testPatternPattern =
                ImpliesF
                    Implies
                        { impliesSort = testedSort
                        , impliesFirst = anotherUnifiedPattern
                        , impliesSecond = testedUnifiedPattern
                        }
            , testPatternSort = testedSort
            , testPatternErrorStack = ErrorStack ["\\implies (<test data>)"]
            }
        , TestPattern
            { testPatternPattern =
                InF
                    In
                        { inOperandSort = testedSort
                        , inResultSort = resultSort
                        , inContainedChild = testedUnifiedPattern
                        , inContainingChild = anotherUnifiedPattern
                        }
            , testPatternSort = resultSort
            , testPatternErrorStack = ErrorStack ["\\in (<test data>)"]
            }
        , TestPattern
            { testPatternPattern =
                InF
                    In
                        { inOperandSort = testedSort
                        , inResultSort = resultSort
                        , inContainedChild = anotherUnifiedPattern
                        , inContainingChild = testedUnifiedPattern
                        }
            , testPatternSort = resultSort
            , testPatternErrorStack = ErrorStack ["\\in (<test data>)"]
            }
        , TestPattern
            { testPatternPattern =
                NotF
                    Not
                        { notSort = testedSort
                        , notChild = testedUnifiedPattern
                        }
            , testPatternSort = testedSort
            , testPatternErrorStack = ErrorStack ["\\not (<test data>)"]
            }
        , TestPattern
            { testPatternPattern =
                OrF
                    Or
                        { orSort = testedSort
                        , orChildren = [testedUnifiedPattern, anotherUnifiedPattern]
                        }
            , testPatternSort = testedSort
            , testPatternErrorStack = ErrorStack ["\\or (<test data>)"]
            }
        , TestPattern
            { testPatternPattern =
                OrF
                    Or
                        { orSort = testedSort
                        , orChildren = [anotherUnifiedPattern, testedUnifiedPattern]
                        }
            , testPatternSort = testedSort
            , testPatternErrorStack = ErrorStack ["\\or (<test data>)"]
            }
        ]
      where
        anotherUnifiedPattern = embedParsedPattern anotherPattern
        testedUnifiedPattern = embedParsedPattern testedPattern

patternInUnquantifiedObjectPatterns ::
    PatternF VariableName ParsedPattern ->
    PatternF VariableName ParsedPattern ->
    OperandSort ->
    [TestPattern]
patternInUnquantifiedObjectPatterns
    testedPattern
    anotherPattern
    (OperandSort testedSort) =
        [ TestPattern
            { testPatternPattern =
                NextF
                    Next
                        { nextSort = testedSort
                        , nextChild = testedUnifiedPattern
                        }
            , testPatternSort = testedSort
            , testPatternErrorStack = ErrorStack ["\\next (<test data>)"]
            }
        , TestPattern
            { testPatternPattern =
                RewritesF
                    Rewrites
                        { rewritesSort = testedSort
                        , rewritesFirst = testedUnifiedPattern
                        , rewritesSecond = anotherUnifiedPattern
                        }
            , testPatternSort = testedSort
            , testPatternErrorStack = ErrorStack ["\\rewrites (<test data>)"]
            }
        , TestPattern
            { testPatternPattern =
                RewritesF
                    Rewrites
                        { rewritesSort = testedSort
                        , rewritesFirst = anotherUnifiedPattern
                        , rewritesSecond = testedUnifiedPattern
                        }
            , testPatternSort = testedSort
            , testPatternErrorStack = ErrorStack ["\\rewrites (<test data>)"]
            }
        ]
      where
        anotherUnifiedPattern = embedParsedPattern anotherPattern
        testedUnifiedPattern = embedParsedPattern testedPattern

testsForUnifiedPatternInTopLevelContext ::
    NamePrefix ->
    DeclaredSort ->
    SortVariablesThatMustBeDeclared ->
    SortVariablesThatMustBeDeclared ->
    [ParsedSentence] ->
    PatternRestrict ->
    [TestPattern -> TestData]
testsForUnifiedPatternInTopLevelContext
    namePrefix
    additionalSort
    sortVariables
    _ =
        testsForUnifiedPatternInTopLevelGenericContext
            namePrefix
            additionalSort
            sortVariables

testsForUnifiedPatternInTopLevelGenericContext ::
    NamePrefix ->
    DeclaredSort ->
    SortVariablesThatMustBeDeclared ->
    [ParsedSentence] ->
    PatternRestrict ->
    [TestPattern -> TestData]
testsForUnifiedPatternInTopLevelGenericContext
    (NamePrefix _)
    (DeclaredSort _)
    (SortVariablesThatMustBeDeclared sortVariables)
    additionalSentences
    patternRestrict =
        let axiomPattern testPattern =
                TestData
                    { testDataDescription = "Pattern in axiom"
                    , testDataError =
                        Error
                            ( "module 'MODULE'"
                                : "axiom declaration"
                                : testPatternErrorStackStrings testPattern
                            )
                            defaultErrorMessage
                    , testDataDefinition =
                        simpleDefinitionFromSentences
                            (ModuleName "MODULE")
                            ( axiomSentenceWithParamsAndAttrs
                                (testPatternUnverifiedPattern testPattern)
                                sortVariables
                                [simplificationAttribute Nothing]
                                : additionalSentences
                            )
                    }
         in case patternRestrict of
                NeedsInternalDefinitions -> [axiomPattern]
                NeedsSortedParent -> [axiomPattern]

defaultErrorMessage :: String
defaultErrorMessage = "Replace this with a real error message."

-- MLPatternType
-- Application
-- axiom
-- attributes -- module and definition
