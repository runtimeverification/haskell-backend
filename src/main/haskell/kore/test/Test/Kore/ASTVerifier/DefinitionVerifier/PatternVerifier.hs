module Test.Kore.ASTVerifier.DefinitionVerifier.PatternVerifier
    ( test_patternVerifier
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( HasCallStack )

import qualified Data.List as List

import           Kore.AST.AstWithLocation
import           Kore.AST.Kore
import           Kore.AST.Pure
import           Kore.AST.PureToKore
import           Kore.AST.Sentence
import           Kore.AST.Valid
import qualified Kore.Attribute.Hook as Attribute.Hook
import qualified Kore.Domain.Builtin as Domain
import           Kore.Error
import           Kore.Implicit.ImplicitSorts
import           Kore.MetaML.AST

import Test.Kore
import Test.Kore.ASTVerifier.DefinitionVerifier as Helpers

data PatternRestrict
    = NeedsInternalDefinitions
    | NeedsSortedParent

data TestPattern level = TestPattern
    { testPatternPattern
        :: !(Pattern level Domain.Builtin Variable VerifiedKorePattern)
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
    :: MetaOrObject level => TestPattern level -> VerifiedKorePattern
testPatternUnifiedPattern
    TestPattern { testPatternPattern, testPatternSort }
  =
    asKorePattern (valid :< testPatternPattern)
  where
    valid = Valid { patternSort = testPatternSort }

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
        (ApplicationPattern Application
            { applicationSymbolOrAlias = nilSortListHead
            , applicationChildren = []
            }
        )
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
                let valid = Valid { patternSort = objectSort } in
                asKorePattern
                    (valid :< simpleExistsPattern objectVariable' objectSort)
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
                let valid =
                        Valid { patternSort = variableSort anotherVariable }
                in asKorePattern (valid :< VariablePattern anotherVariable)
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
                    ((:<)
                        Valid { patternSort = objectSortVariableSort }
                        (simpleExistsPattern
                            objectVariableSortVariable
                            objectSortVariableSort
                        )
                    )
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
            [ "(<test data>, <implicitly defined entity>)" ]
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
    , failureTestsForObjectPattern "Domain value - INT.Int"
        (ExpectedErrorMessage
            "<string literal>:1:1:\n\
            \unexpected 'a'\n\
            \expecting '+', '-', or integer\n")
        (ErrorStack
            [ "\\dv (<test data>)"
            , "Verifying builtin sort 'INT.Int'"
            , "While parsing domain value"
            ]
        )
        (DomainValuePattern DomainValue
            { domainValueSort = intSort
            , domainValueChild =
                Domain.BuiltinPattern
                    $ Kore.AST.Pure.eraseAnnotations
                    $ mkStringLiteral "abcd"  -- Not a decimal integer
            }
        )
        (NamePrefix "dummy")
        (TestedPatternSort (updateAstLocation intSort AstLocationTest))
        (SortVariablesThatMustBeDeclared [])
        (DeclaredSort intSort)
        [ asSentence intSortSentence ]
        NeedsInternalDefinitions
    , successTestsForObjectPattern "Domain value - INT.Int - Negative"
        (DomainValuePattern DomainValue
            { domainValueSort = intSort
            , domainValueChild =
                Domain.BuiltinPattern
                $ Kore.AST.Pure.eraseAnnotations
                $ mkStringLiteral "-256"
            }
        )
        (NamePrefix "dummy")
        (TestedPatternSort intSort)
        (SortVariablesThatMustBeDeclared [])
        (DeclaredSort intSort)
        [ asSentence intSortSentence ]
        NeedsInternalDefinitions
    , successTestsForObjectPattern "Domain value - INT.Int - Positive (unsigned)"
        (DomainValuePattern DomainValue
            { domainValueSort = intSort
            , domainValueChild =
                Domain.BuiltinPattern
                $ Kore.AST.Pure.eraseAnnotations
                $ mkStringLiteral "1024"
            }
        )
        (NamePrefix "dummy")
        (TestedPatternSort intSort)
        (SortVariablesThatMustBeDeclared [])
        (DeclaredSort intSort)
        [ asSentence intSortSentence ]
        NeedsInternalDefinitions
    , successTestsForObjectPattern "Domain value - INT.Int - Positive (signed)"
        (DomainValuePattern DomainValue
            { domainValueSort = intSort
            , domainValueChild =
                Domain.BuiltinPattern
                $ Kore.AST.Pure.eraseAnnotations
                $ mkStringLiteral "+128"
            }
        )
        (NamePrefix "dummy")
        (TestedPatternSort intSort)
        (SortVariablesThatMustBeDeclared [])
        (DeclaredSort intSort)
        [ asSentence intSortSentence ]
        NeedsInternalDefinitions
    , failureTestsForObjectPattern "Domain value - BOOL.Bool"
        (ExpectedErrorMessage
            "<string literal>:1:1:\n\
            \unexpected \"untru\"\n\
            \expecting \"false\" or \"true\"\n")
        (ErrorStack
            [ "\\dv (<test data>)"
            , "Verifying builtin sort 'BOOL.Bool'"
            , "While parsing domain value"
            ]
        )
        (DomainValuePattern DomainValue
            { domainValueSort = boolSort
            , domainValueChild =
                Domain.BuiltinPattern
                    $ Kore.AST.Pure.eraseAnnotations
                    $ mkStringLiteral "untrue"  -- Not a BOOL.Bool
            }
        )
        (NamePrefix "dummy")
        (TestedPatternSort (updateAstLocation boolSort AstLocationTest))
        (SortVariablesThatMustBeDeclared [])
        (DeclaredSort boolSort)
        [ asSentence boolSortSentence ]
        NeedsInternalDefinitions
    , successTestsForObjectPattern "Domain value - BOOL.Bool - true"
        (DomainValuePattern DomainValue
            { domainValueSort = boolSort
            , domainValueChild =
                Domain.BuiltinPattern
                    $ Kore.AST.Pure.eraseAnnotations
                    $ mkStringLiteral "true"
            }
        )
        (NamePrefix "dummy")
        (TestedPatternSort (updateAstLocation boolSort AstLocationTest))
        (SortVariablesThatMustBeDeclared [])
        (DeclaredSort boolSort)
        [ asSentence boolSortSentence ]
        NeedsInternalDefinitions
    , successTestsForObjectPattern "Domain value - BOOL.Bool - false"
        (DomainValuePattern DomainValue
            { domainValueSort = boolSort
            , domainValueChild =
                Domain.BuiltinPattern
                    $ Kore.AST.Pure.eraseAnnotations
                    $ mkStringLiteral "false"
            }
        )
        (NamePrefix "dummy")
        (TestedPatternSort (updateAstLocation boolSort AstLocationTest))
        (SortVariablesThatMustBeDeclared [])
        (DeclaredSort boolSort)
        [ asSentence boolSortSentence ]
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
            objectAliasName
            objectSort
            [ Variable
                { variableName = testId "x"
                , variableSort = anotherObjectSort2
                }
            ]
    objectSortVariable = sortVariable @Object "ObjectSortVariable"
    objectSortVariableSort :: Sort Object
    objectSortVariableSort = sortVariableSort "ObjectSortVariable"
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
            :: VerifiedKoreSentenceSymbol Object)
    intSortName = SortName "Int"
    intSort :: Sort Object
    intSort = simpleSort intSortName
    intSortSentence :: VerifiedKoreSentenceHook
    intSortSentence =
        SentenceHookedSort SentenceSort
            { sentenceSortName = testId name
            , sentenceSortParameters = []
            , sentenceSortAttributes =
                Attributes [ Attribute.Hook.hookAttribute "INT.Int" ]
            }
      where
        SortName name = intSortName
    boolSortName = SortName "Int"
    boolSort :: Sort Object
    boolSort = simpleSort boolSortName
    boolSortSentence :: VerifiedKoreSentenceHook
    boolSortSentence =
        SentenceHookedSort SentenceSort
            { sentenceSortName = testId name
            , sentenceSortParameters = []
            , sentenceSortAttributes =
                Attributes [ Attribute.Hook.hookAttribute "BOOL.Bool" ]
            }
      where
        SortName name = boolSortName

dummyVariableAndSentences
    :: NamePrefix
    -> (Variable Object, [VerifiedKoreSentence])
dummyVariableAndSentences (NamePrefix namePrefix) =
    (dummyVariable, [simpleSortSentence dummySortName])
  where
    dummySortName = SortName (namePrefix <> "_OtherSort")
    dummySort' = simpleSort dummySortName
    dummyVariable =
        variable (VariableName (namePrefix <> "_OtherVariable")) dummySort'


successTestsForObjectPattern
    :: String
    -> Pattern Object Domain.Builtin Variable VerifiedKorePattern
    -> NamePrefix
    -> TestedPatternSort Object
    -> SortVariablesThatMustBeDeclared Object
    -> DeclaredSort Object
    -> [VerifiedKoreSentence]
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
    -> Pattern Meta Domain.Builtin Variable VerifiedKorePattern
    -> NamePrefix
    -> TestedPatternSort Meta
    -> SortVariablesThatMustBeDeclared Meta
    -> SortVariablesThatMustBeDeclared Object
    -> DeclaredSort Meta
    -> VariableOfDeclaredSort Meta
    -> [VerifiedKoreSentence]
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
    -> Pattern Object Domain.Builtin Variable VerifiedKorePattern
    -> NamePrefix
    -> TestedPatternSort Object
    -> SortVariablesThatMustBeDeclared Object
    -> DeclaredSort Object
    -> [VerifiedKoreSentence]
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
    dummySortName = SortName (rawNamePrefix <> "_OtherSort")
    dummySort' = simpleSort dummySortName
    dummyVariable =
        variable (VariableName (rawNamePrefix <> "_OtherVariable")) dummySort'
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
    -> Pattern Meta Domain.Builtin Variable VerifiedKorePattern
    -> NamePrefix
    -> TestedPatternSort Meta
    -> SortVariablesThatMustBeDeclared Meta
    -> SortVariablesThatMustBeDeclared Object
    -> DeclaredSort Meta
    -> VariableOfDeclaredSort Meta
    -> [VerifiedKoreSentence]
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
    -> Pattern level Domain.Builtin Variable VerifiedKorePattern
    -> NamePrefix
    -> TestedPatternSort level
    -> SortVariablesThatMustBeDeclared level
    -> SortVariablesThatMustBeDeclared Object
    -> DeclaredSort level
    -> VariableOfDeclaredSort level
    -> [VerifiedKoreSentence]
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
            , existsChild =
                let var = VariablePattern anotherVariable
                    valid = Valid { patternSort = testedSort }
                in asKorePattern (valid :< var)
            }
    anotherVariable =
        Variable
            { variableName = testId (namePrefix <> "_anotherVar")
            , variableSort = testedSort
            }
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

objectPatternInAllContexts
    :: Pattern Object Domain.Builtin Variable VerifiedKorePattern
    -> NamePrefix
    -> TestedPatternSort Object
    -> SortVariablesThatMustBeDeclared Object
    -> DeclaredSort Object
    -> [VerifiedKoreSentence]
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
            , existsChild =
                let var = VariablePattern anotherVariable
                    valid = Valid { patternSort = testedSort }
                in asKorePattern (valid :< var)
            }
    anotherVariable =
        Variable
            { variableName = testId (namePrefix <> "_anotherVar")
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
    -> [VerifiedKoreSentence]
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
    aliasSentence :: VerifiedKoreSentence
    aliasSentence =
        let aliasConstructor = testId rawAliasName
            aliasParams = [SortVariable (testId rawSortVariableName)]
        in (sentencePureToKore . SentenceAliasSentence)
            SentenceAlias
                { sentenceAliasAlias = Alias { aliasConstructor, aliasParams }
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
                            [ Variable
                                { variableName = testId "x"
                                , variableSort = symbolAliasSort
                                }
                            ]
                        }
                , sentenceAliasRightPattern =
                    let top' = TopPattern Top { topSort = anotherSort }
                        valid = Valid { patternSort = anotherSort }
                    in asPurePattern (valid :< top')
                , sentenceAliasAttributes = Attributes []
                }

genericPatternInPatterns
    :: MetaOrObject level
    => Pattern level Domain.Builtin Variable VerifiedKorePattern
    -> Pattern level Domain.Builtin Variable VerifiedKorePattern
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
                , applicationChildren = [asKorePattern (valid :< testedPattern)]
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
            { testPatternPattern = ApplicationPattern Application
                { applicationSymbolOrAlias = alias
                , applicationChildren = [asKorePattern (valid :< testedPattern)]
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
  where
    valid = Valid { patternSort = testedSort }

objectPatternInPatterns
    :: Pattern Object Domain.Builtin Variable VerifiedKorePattern
    -> Pattern Object Domain.Builtin Variable VerifiedKorePattern
    -> OperandSort Object
    -> [TestPattern Object]
objectPatternInPatterns = patternInUnquantifiedObjectPatterns

patternInQuantifiedPatterns
    :: MetaOrObject level
    => Pattern level Domain.Builtin Variable VerifiedKorePattern
    -> Sort level
    -> Variable level
    -> [TestPattern level]
patternInQuantifiedPatterns testedPattern testedSort quantifiedVariable =
    [ TestPattern
        { testPatternPattern = ExistsPattern Exists
            { existsSort = testedSort
            , existsVariable = quantifiedVariable
            , existsChild = testedKorePattern
            }
        , testPatternSort = testedSort
        , testPatternErrorStack =
            ErrorStack
                [ "\\exists '"
                    ++ getIdForError (variableName quantifiedVariable)
                    ++ "' (<test data>)"
                ]
        }
    , TestPattern
        { testPatternPattern = ForallPattern Forall
            { forallSort = testedSort
            , forallVariable = quantifiedVariable
            , forallChild = testedKorePattern
            }
        , testPatternSort = testedSort
        , testPatternErrorStack =
            ErrorStack
                [ "\\forall '"
                    ++ getIdForError (variableName quantifiedVariable)
                    ++ "' (<test data>)"
                ]
        }
    ]
  where
    valid = Valid { patternSort = testedSort }
    testedKorePattern = asKorePattern (valid :< testedPattern)

patternInUnquantifiedGenericPatterns
    :: MetaOrObject level
    => Pattern level Domain.Builtin Variable VerifiedKorePattern
    -> Pattern level Domain.Builtin Variable VerifiedKorePattern
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
    valid = Valid { patternSort = testedSort }
    anotherUnifiedPattern = asKorePattern (valid :< anotherPattern)
    testedUnifiedPattern = asKorePattern (valid :< testedPattern)

patternInUnquantifiedObjectPatterns
    :: Pattern Object Domain.Builtin Variable VerifiedKorePattern
    -> Pattern Object Domain.Builtin Variable VerifiedKorePattern
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
    valid = Valid { patternSort = testedSort }
    anotherUnifiedPattern = asKorePattern (valid :< anotherPattern)
    testedUnifiedPattern = asKorePattern (valid :< testedPattern)

testsForUnifiedPatternInTopLevelContext
    :: MetaOrObject level
    => level
    -> NamePrefix
    -> DeclaredSort level
    -> SortVariablesThatMustBeDeclared level
    -> SortVariablesThatMustBeDeclared Object
    -> [VerifiedKoreSentence]
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
    -> [VerifiedKoreSentence]
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
