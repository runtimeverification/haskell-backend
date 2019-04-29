module Test.Kore.ASTVerifier.DefinitionVerifier.PatternVerifier
    ( test_patternVerifier
    , test_verifyBinder
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit

import qualified Data.Foldable as Foldable
import qualified Data.List as List
import qualified Data.Set as Set

import           Kore.AST.AstWithLocation
import           Kore.AST.Pure
import           Kore.AST.Sentence
import           Kore.AST.Valid
import           Kore.ASTVerifier.PatternVerifier as PatternVerifier
import qualified Kore.Attribute.Hook as Attribute.Hook
import qualified Kore.Domain.Builtin as Domain
import           Kore.Error
import           Kore.IndexedModule.Error
                 ( noSort )
import           Kore.Step.TermLike hiding
                 ( freeVariables )
import           Kore.Syntax.StringLiteral
import qualified Kore.Verified as Verified

import           Test.Kore
import           Test.Kore.ASTVerifier.DefinitionVerifier as Helpers
import qualified Test.Kore.Builtin.Builtin as Builtin
import qualified Test.Kore.Builtin.Definition as Builtin

data PatternRestrict
    = NeedsInternalDefinitions
    | NeedsSortedParent

data TestPattern level = TestPattern
    { testPatternPattern
        :: !(Pattern level Domain.Builtin Variable (TermLike Variable))
    , testPatternSort       :: !Sort
    , testPatternErrorStack :: !ErrorStack
    }

newtype VariableOfDeclaredSort level = VariableOfDeclaredSort (Variable)

testPatternErrorStackStrings :: TestPattern Object -> [String]
testPatternErrorStackStrings
    TestPattern {testPatternErrorStack = ErrorStack strings}
  =
    strings

testPatternUnifiedPattern :: TestPattern Object -> TermLike Variable
testPatternUnifiedPattern
    TestPattern { testPatternPattern, testPatternSort }
  =
    asPurePattern (valid :< testPatternPattern)
  where
    valid =
        Valid
            { patternSort = testPatternSort
            , freeVariables =
                Foldable.foldl'
                    Set.union
                    Set.empty
                    (freeVariables . extract <$> testPatternPattern)
            }

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
    , failureTestsForObjectPattern "Object pattern - sort not defined"
        (ExpectedErrorMessage $ noSort "ObjectSort")
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
                let
                    valid = Valid { patternSort, freeVariables }
                      where
                        patternSort = objectSort
                        freeVariables = Set.empty
                    pattern' = simpleExistsPattern objectVariable' objectSort
                in
                    asPurePattern (valid :< pattern')
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
            , existsChild = (mkVar anotherVariable)
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
                asPurePattern
                    ((:<)
                        Valid
                            { patternSort = objectSortVariableSort
                            , freeVariables = Set.empty
                            }
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
        (ExpectedErrorMessage $ noSort "#InvalidMetaSort")
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
            "Expecting sort '#Char{}' but got '#String{}'.")
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
        (TestedPatternSort stringMetaSort)
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
            "Expecting sort '#Char{}' but got '#String{}'.")
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
            \  |\n\
            \1 | abcd\n\
            \  | ^\n\
            \unexpected 'a'\n\
            \expecting '+', '-', or integer\n")
        (ErrorStack
            [ "\\dv (<test data>)"
            , "Verifying builtin sort 'INT.Int'"
            , "While parsing domain value"
            ]
        )
        (DomainValuePattern $ Domain.BuiltinExternal
            Domain.External
                { domainValueSort = intSort
                , domainValueChild =
                    Kore.AST.Pure.eraseAnnotations
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
        (DomainValuePattern $ Domain.BuiltinExternal
            Domain.External
                { domainValueSort = intSort
                , domainValueChild =
                    Kore.AST.Pure.eraseAnnotations
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
        (DomainValuePattern $ Domain.BuiltinExternal
            Domain.External
                { domainValueSort = intSort
                , domainValueChild =
                    Kore.AST.Pure.eraseAnnotations
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
        (DomainValuePattern $ Domain.BuiltinExternal
            Domain.External
                { domainValueSort = intSort
                , domainValueChild =
                    Kore.AST.Pure.eraseAnnotations
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
            \  |\n\
            \1 | untrue\n\
            \  | ^^^^^\n\
            \unexpected \"untru\"\n\
            \expecting \"false\" or \"true\"\n")
        (ErrorStack
            [ "\\dv (<test data>)"
            , "Verifying builtin sort 'BOOL.Bool'"
            , "While parsing domain value"
            ]
        )
        (DomainValuePattern $ Domain.BuiltinExternal
            Domain.External
                { domainValueSort = boolSort
                , domainValueChild =
                    Kore.AST.Pure.eraseAnnotations
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
        (DomainValuePattern $ Domain.BuiltinExternal
            Domain.External
                { domainValueSort = boolSort
                , domainValueChild =
                    Kore.AST.Pure.eraseAnnotations
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
        (DomainValuePattern $ Domain.BuiltinExternal
            Domain.External
                { domainValueSort = boolSort
                , domainValueChild =
                    Kore.AST.Pure.eraseAnnotations
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
    objectSort :: Sort
    objectSort = simpleSort objectSortName
    objectVariableName = VariableName "ObjectVariable"
    objectVariable' = variable objectVariableName objectSort
    objectSortSentence = simpleSortSentence objectSortName
    metaSort1 = updateAstLocation stringMetaSort AstLocationTest
    metaVariable' = variable (VariableName "#MetaVariable") metaSort1
    dummyMetaSort = updateAstLocation charMetaSort AstLocationTest
    dummyMetaVariable = variable (VariableName "#otherVariable") dummyMetaSort
    anotherSortName = SortName "anotherSort"
    anotherSort :: Sort
    anotherSort = simpleSort anotherSortName
    anotherVariable = variable objectVariableName anotherSort
    anotherSortSentence = simpleSortSentence anotherSortName
    anotherMetaSort = updateAstLocation stringMetaSort AstLocationTest
    anotherObjectSortName2 = SortName "anotherSort2"
    anotherObjectSort2 :: Sort
    anotherObjectSort2 = simpleSort anotherObjectSortName2
    anotherObjectSortSentence2 = simpleSortSentence anotherObjectSortName2
    invalidMetaSort :: Sort
    invalidMetaSort = simpleSort (SortName "#InvalidMetaSort")
    anotherMetaSort2 = updateAstLocation charMetaSort AstLocationTest
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
                , variableCounter = mempty
                , variableSort = anotherObjectSort2
                }
            ]
    objectSortVariable = sortVariable "ObjectSortVariable"
    objectSortVariableSort :: Sort
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
            :: Verified.SentenceSymbol)
    intSortName = SortName "Int"
    intSort :: Sort
    intSort = simpleSort intSortName
    intSortSentence :: Verified.SentenceHook
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
    boolSort :: Sort
    boolSort = simpleSort boolSortName
    boolSortSentence :: Verified.SentenceHook
    boolSortSentence =
        SentenceHookedSort SentenceSort
            { sentenceSortName = testId name
            , sentenceSortParameters = []
            , sentenceSortAttributes =
                Attributes [ Attribute.Hook.hookAttribute "BOOL.Bool" ]
            }
      where
        SortName name = boolSortName

test_verifyBinder :: [TestTree]
test_verifyBinder =
    [ testVerifyExists
    , testVerifyForall
    ]
  where
    context =
        PatternVerifier.Context
            { declaredVariables = PatternVerifier.emptyDeclaredVariables
            , declaredSortVariables = Set.empty
            , indexedModule = Builtin.indexedModule
            , builtinDomainValueVerifiers = mempty
            }
    testVerifyBinder name expect =
        testCase name $ do
            let
                original = eraseAnnotations expect
                verifier = verifyStandalonePattern Nothing original
                Right actual = runPatternVerifier context verifier
            assertEqual "" expect actual
            assertEqual "" (extract expect) (extract actual)
    testVerifyExists =
        testVerifyBinder "verifyExists" expect
      where
        x = varS "x" Builtin.intSort
        expect = mkExists x (mkVar x)
    testVerifyForall =
        testVerifyBinder "verifyForall" expect
      where
        x = varS "x" Builtin.intSort
        expect = mkForall x (mkVar x)

dummyVariableAndSentences
    :: NamePrefix
    -> (Variable, [Verified.Sentence])
dummyVariableAndSentences (NamePrefix namePrefix) =
    (dummyVariable, [simpleSortSentence dummySortName])
  where
    dummySortName = SortName (namePrefix <> "_OtherSort")
    dummySort' = simpleSort dummySortName
    dummyVariable =
        variable (VariableName (namePrefix <> "_OtherVariable")) dummySort'


successTestsForObjectPattern
    :: String
    -> Pattern Object Domain.Builtin Variable (TermLike Variable)
    -> NamePrefix
    -> TestedPatternSort Object
    -> SortVariablesThatMustBeDeclared Object
    -> DeclaredSort Object
    -> [Verified.Sentence]
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
    -> Pattern Meta Domain.Builtin Variable (TermLike Variable)
    -> NamePrefix
    -> TestedPatternSort Meta
    -> SortVariablesThatMustBeDeclared Meta
    -> SortVariablesThatMustBeDeclared Object
    -> DeclaredSort Meta
    -> VariableOfDeclaredSort Meta
    -> [Verified.Sentence]
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
    -> Pattern Object Domain.Builtin Variable (TermLike Variable)
    -> NamePrefix
    -> TestedPatternSort Object
    -> SortVariablesThatMustBeDeclared Object
    -> DeclaredSort Object
    -> [Verified.Sentence]
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
    -> Pattern Meta Domain.Builtin Variable (TermLike Variable)
    -> NamePrefix
    -> TestedPatternSort Meta
    -> SortVariablesThatMustBeDeclared Meta
    -> SortVariablesThatMustBeDeclared Object
    -> DeclaredSort Meta
    -> VariableOfDeclaredSort Meta
    -> [Verified.Sentence]
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
    :: Pattern Object Domain.Builtin Variable (TermLike Variable)
    -> NamePrefix
    -> TestedPatternSort Object
    -> SortVariablesThatMustBeDeclared Object
    -> SortVariablesThatMustBeDeclared Object
    -> DeclaredSort Object
    -> VariableOfDeclaredSort Object
    -> [Verified.Sentence]
    -> PatternRestrict
    -> [TestData]
genericPatternInAllContexts
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
            , existsChild = (mkVar anotherVariable)
            }
    anotherVariable =
        Variable
            { variableName = testId (namePrefix <> "_anotherVar")
            , variableCounter = mempty
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
    :: Pattern Object Domain.Builtin Variable (TermLike Variable)
    -> NamePrefix
    -> TestedPatternSort Object
    -> SortVariablesThatMustBeDeclared Object
    -> DeclaredSort Object
    -> [Verified.Sentence]
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
            , existsChild = (mkVar anotherVariable)
            }
    anotherVariable =
        Variable
            { variableName = testId (namePrefix <> "_anotherVar")
            , variableCounter = mempty
            , variableSort = testedSort
            }

patternsInAllContexts
    :: [TestPattern Object]
    -> NamePrefix
    -> SortVariablesThatMustBeDeclared Object
    -> SortVariablesThatMustBeDeclared Object
    -> DeclaredSort Object
    -> [Verified.Sentence]
    -> PatternRestrict
    -> [TestData]
patternsInAllContexts
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
        SentenceSymbolSentence SentenceSymbol
                { sentenceSymbolSymbol = Symbol
                    { symbolConstructor = testId rawSymbolName
                    , symbolParams = [SortVariable (testId rawSortVariableName)]
                    }
                , sentenceSymbolSorts = [symbolAliasSort]
                , sentenceSymbolResultSort = anotherSort
                , sentenceSymbolAttributes =
                    Attributes []
                }
    aliasSentence :: Verified.Sentence
    aliasSentence =
        let aliasConstructor = testId rawAliasName
            aliasParams = [SortVariable (testId rawSortVariableName)]
        in SentenceAliasSentence
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
                                , variableCounter = mempty
                                , variableSort = symbolAliasSort
                                }
                            ]
                        }
                , sentenceAliasRightPattern = mkTop anotherSort
                , sentenceAliasAttributes = Attributes []
                }

genericPatternInPatterns
    :: Pattern Object Domain.Builtin Variable (TermLike Variable)
    -> Pattern Object Domain.Builtin Variable (TermLike Variable)
    -> OperandSort Object
    -> Helpers.ResultSort Object
    -> VariableOfDeclaredSort Object
    -> SymbolOrAlias Object
    -> SymbolOrAlias Object
    -> PatternRestrict
    -> [TestPattern Object]
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
                , applicationChildren = [asPurePattern (valid :< testedPattern)]
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
                , applicationChildren = [asPurePattern (valid :< testedPattern)]
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
    valid =
        Valid
            { patternSort = testedSort
            , freeVariables =
                Foldable.foldl'
                    Set.union
                    Set.empty
                    (freeVariables . extract <$> testedPattern)
            }

objectPatternInPatterns
    :: Pattern Object Domain.Builtin Variable (TermLike Variable)
    -> Pattern Object Domain.Builtin Variable (TermLike Variable)
    -> OperandSort Object
    -> [TestPattern Object]
objectPatternInPatterns = patternInUnquantifiedObjectPatterns

patternInQuantifiedPatterns
    :: Pattern Object Domain.Builtin Variable (TermLike Variable)
    -> Sort
    -> Variable
    -> [TestPattern Object]
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
    valid =
        Valid
            { patternSort = testedSort
            , freeVariables =
                Foldable.foldl'
                    Set.union
                    Set.empty
                    (freeVariables . extract <$> testedPattern)
            }
    testedKorePattern = asPurePattern (valid :< testedPattern)

patternInUnquantifiedGenericPatterns
    :: Pattern Object Domain.Builtin Variable (TermLike Variable)
    -> Pattern Object Domain.Builtin Variable (TermLike Variable)
    -> OperandSort Object
    -> Helpers.ResultSort Object
    -> [TestPattern Object]
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
    valid =
        Valid
            { patternSort = testedSort
            , freeVariables =
                Foldable.foldl'
                    Set.union
                    Set.empty
                    (unifiedFreeVariables . extract <$> testedPattern)
            }
    unifiedFreeVariables = freeVariables
    anotherUnifiedPattern = asPurePattern (valid :< anotherPattern)
    testedUnifiedPattern = asPurePattern (valid :< testedPattern)

patternInUnquantifiedObjectPatterns
    :: Pattern Object Domain.Builtin Variable (TermLike Variable)
    -> Pattern Object Domain.Builtin Variable (TermLike Variable)
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
    valid =
        Valid
            { patternSort = testedSort
            , freeVariables =
                Foldable.foldl'
                    Set.union
                    Set.empty
                    (unifiedFreeVariables . extract <$> testedPattern)
            }
    unifiedFreeVariables = freeVariables
    anotherUnifiedPattern = asPurePattern (valid :< anotherPattern)
    testedUnifiedPattern = asPurePattern (valid :< testedPattern)

testsForUnifiedPatternInTopLevelContext
    :: NamePrefix
    -> DeclaredSort Object
    -> SortVariablesThatMustBeDeclared Object
    -> SortVariablesThatMustBeDeclared Object
    -> [Verified.Sentence]
    -> PatternRestrict
    -> [TestPattern Object -> TestData]
testsForUnifiedPatternInTopLevelContext
    namePrefix
    additionalSort
    sortVariables
    _
  =
    testsForUnifiedPatternInTopLevelGenericContext
        namePrefix
        additionalSort
        sortVariables

testsForUnifiedPatternInTopLevelGenericContext
    :: NamePrefix
    -> DeclaredSort Object
    -> SortVariablesThatMustBeDeclared Object
    -> [Verified.Sentence]
    -> PatternRestrict
    -> [TestPattern Object -> TestData]
testsForUnifiedPatternInTopLevelGenericContext
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
                        sortVariables
                    : additionalSentences
                    )
            }
    in case patternRestrict of
        NeedsInternalDefinitions -> [axiomPattern]
        NeedsSortedParent        -> [axiomPattern]

defaultErrorMessage :: String
defaultErrorMessage = "Replace this with a real error message."


    -- MLPatternType
    -- Application
    -- axiom
    -- attributes -- module and definition
