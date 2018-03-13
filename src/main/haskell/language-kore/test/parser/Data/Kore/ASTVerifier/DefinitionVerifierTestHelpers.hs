module Data.Kore.ASTVerifier.DefinitionVerifierTestHelpers where

import           Test.Tasty                               (TestTree, testGroup)
import           Test.Tasty.HUnit                         (assertEqual,
                                                           assertFailure,
                                                           testCase)


import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.ASTPrettyPrint
import           Data.Kore.ASTVerifier.DefinitionVerifier
import           Data.Kore.ASTVerifier.Error
import           Data.Kore.Error
import           Data.Kore.Unparser.Unparse

newtype ExpectedErrorMessage = ExpectedErrorMessage String
newtype ErrorStack = ErrorStack [String]

data TestData = TestData
    { testDataDescription :: !String
    , testDataError       :: !(Error VerifyError)
    , testDataDefinition  :: !Definition
    }

addPrefixToDescription :: String -> [TestData] -> [TestData]
addPrefixToDescription prefix =
    map
        (\t -> t {testDataDescription = prefix ++ testDataDescription t})

failureTestDataGroup
    :: String -> ExpectedErrorMessage -> ErrorStack -> [TestData] -> TestTree
failureTestDataGroup description errorMessage errorStack testData =
    testGroup
        description
        (map (failureTestData errorMessage errorStack) testData)

failureTestData :: ExpectedErrorMessage -> ErrorStack -> TestData -> TestTree
failureTestData
    (ExpectedErrorMessage message)
    (ErrorStack stack)
    testData
  =
    expectFailureWithError
        (testDataDescription testData)
        err
            { errorError = message
            , errorContext = errorContext err ++ stack
            }
        (testDataDefinition testData)
  where
    err = testDataError testData

successTestDataGroup :: String -> [TestData] -> TestTree
successTestDataGroup description testDatas =
    testGroup description (map successTestData testDatas)

successTestData :: TestData -> TestTree
successTestData testData =
    expectSuccess (testDataDescription testData) (testDataDefinition testData)

expectSuccess :: String -> Definition -> TestTree
expectSuccess description definition =
    testCase
        description
        (assertEqual
            (  "Expecting verification success! Definition:\n"
            ++ printDefinition definition
            )
            verifySuccess
            (verifyDefinition definition)
        )

expectFailureWithError :: String -> Error VerifyError -> Definition -> TestTree
expectFailureWithError description expectedError definition =
    testCase
        description
        ( case verifyDefinition definition of
            Right _ ->
                assertFailure
                    (  "Expecting verification failure! Definition:\n"
                    ++ printDefinition definition
                    )
            Left actualError ->
                assertEqual
                    ( "Expecting a certain error! Definition:\n"
                    ++ printDefinition definition
                    )
                    expectedError actualError
        )

printDefinition :: Definition -> String
printDefinition definition =
    prettyPrintToString definition
    ++ "\n----------------------\n"
    ++ unparseToString definition
    ++ "\n----------------------"

-------------------------------------------------------------

newtype AliasName = AliasName String
newtype SymbolName = SymbolName String
newtype SortName = SortName String
newtype SortVariableName = SortVariableName String
newtype VariableName = VariableName String
newtype NamePrefix = NamePrefix String
newtype OperandSort level = OperandSort (Sort level)
newtype ResultSort level = ResultSort (Sort level)
newtype DeclaredSort level = DeclaredSort (Sort level)
newtype TestedPatternSort level = TestedPatternSort (Sort level)
newtype SortVariablesThatMustBeDeclared level =
    SortVariablesThatMustBeDeclared [SortVariable level]

simpleDefinitionFromSentences :: ModuleName -> [Sentence] -> Definition
simpleDefinitionFromSentences name sentences =
    Definition
        { definitionAttributes = Attributes []
        , definitionModules =
            [ Module
                { moduleName = name
                , moduleSentences = sentences
                , moduleAttributes = Attributes []
                }
            ]
        }

simpleSortSentence :: SortName -> Sentence
simpleSortSentence (SortName name) =
    SentenceSortSentence SentenceSort
        { sentenceSortName = Id name
        , sentenceSortParameters = []
        , sentenceSortAttributes = Attributes []
        }

simpleMetaAliasSentence :: AliasName -> SortName -> Sentence
simpleMetaAliasSentence alias sort =
    MetaSentenceAliasSentence (simpleAliasSentence alias sort)

simpleObjectAliasSentence :: AliasName -> SortName -> Sentence
simpleObjectAliasSentence alias sort =
    ObjectSentenceAliasSentence (simpleAliasSentence alias sort)

simpleAliasSentence :: AliasName -> SortName -> KoreSentenceAlias level
simpleAliasSentence (AliasName name) (SortName sort) =
    SentenceAlias
        { sentenceAliasAlias = Alias
            { aliasConstructor = Id name
            , aliasParams = []
            }
        , sentenceAliasSorts = []
        , sentenceAliasResultSort =
            SortActualSort SortActual
                { sortActualName = Id sort
                , sortActualSorts = []
                }
        , sentenceAliasAttributes = Attributes []
        }

simpleMetaSymbolSentence :: SymbolName -> SortName -> Sentence
simpleMetaSymbolSentence name sort =
    MetaSentenceSymbolSentence (simpleSymbolSentence name sort)

simpleObjectSymbolSentence :: SymbolName -> SortName -> Sentence
simpleObjectSymbolSentence name sort =
    ObjectSentenceSymbolSentence (simpleSymbolSentence name sort)

simpleSymbolSentence :: SymbolName -> SortName -> KoreSentenceSymbol level
simpleSymbolSentence (SymbolName name) (SortName sort) =
    SentenceSymbol
        { sentenceSymbolSymbol = Symbol
            { symbolConstructor = Id name
            , symbolParams = []
            }
        , sentenceSymbolSorts = []
        , sentenceSymbolResultSort =
            SortActualSort SortActual
                { sortActualName = Id sort
                , sortActualSorts = []
                }
        , sentenceSymbolAttributes = Attributes []
        }

simpleAxiomSentence :: UnifiedPattern -> Sentence
simpleAxiomSentence unifiedPattern =
    SentenceAxiomSentence SentenceAxiom
        { sentenceAxiomParameters = []
        , sentenceAxiomPattern = unifiedPattern
        , sentenceAxiomAttributes = Attributes []
        }

importSentence :: ModuleName -> Sentence
importSentence name =
    SentenceImportSentence SentenceImport
        { sentenceImportModuleName = name
        , sentenceImportAttributes = Attributes []
        }

sortSentenceWithSortParameters :: SortName -> [SortVariable Object] -> Sentence
sortSentenceWithSortParameters (SortName name) parameters =
    SentenceSortSentence SentenceSort
        { sentenceSortName = Id name
        , sentenceSortParameters = parameters
        , sentenceSortAttributes = Attributes []
        }

aliasSentenceWithSort
    :: MetaOrObject level => AliasName -> Sort level -> Sentence
aliasSentenceWithSort (AliasName name) sort =
    asSentenceAliasSentence SentenceAlias
        { sentenceAliasAlias = Alias
            { aliasConstructor = Id name
            , aliasParams = []
            }
        , sentenceAliasSorts = []
        , sentenceAliasResultSort = sort
        , sentenceAliasAttributes = Attributes []
        }

metaAliasSentenceWithSortParameters
    :: AliasName -> Sort Meta -> [SortVariable Meta] -> Sentence
metaAliasSentenceWithSortParameters
    (AliasName name) sort parameters
  =
    MetaSentenceAliasSentence SentenceAlias
        { sentenceAliasAlias = Alias
            { aliasConstructor = Id name
            , aliasParams = parameters
            }
        , sentenceAliasSorts = []
        , sentenceAliasResultSort = sort
        , sentenceAliasAttributes = Attributes []
        }

aliasSentenceWithSortParameters
    :: AliasName -> SortName -> [SortVariable level] -> KoreSentenceAlias level
aliasSentenceWithSortParameters
    (AliasName name) (SortName sort) parameters
  =
    SentenceAlias
        { sentenceAliasAlias = Alias
            { aliasConstructor = Id name
            , aliasParams = parameters
            }
        , sentenceAliasSorts = []
        , sentenceAliasResultSort =
            SortActualSort SortActual
                { sortActualName = Id sort
                , sortActualSorts = []
                }
        , sentenceAliasAttributes = Attributes []
        }

sentenceAliasWithSortArgument
    :: AliasName
    -> Sort level
    -> Sort level
    -> [SortVariable level]
    -> KoreSentenceAlias level
sentenceAliasWithSortArgument
    (AliasName name) sortArgument resultSort parameters
  =
    SentenceAlias
        { sentenceAliasAlias = Alias
            { aliasConstructor = Id name
            , aliasParams = parameters
            }
        , sentenceAliasSorts = [sortArgument]
        , sentenceAliasResultSort = resultSort
        , sentenceAliasAttributes = Attributes []
        }

sentenceAliasWithAttributes
    :: AliasName
    -> [SortVariable level]
    -> Sort level
    -> [UnifiedPattern]
    -> KoreSentenceAlias level
sentenceAliasWithAttributes (AliasName name) params sort attributes =
    SentenceAlias
        { sentenceAliasAlias = Alias
            { aliasConstructor = Id name
            , aliasParams = params
            }
        , sentenceAliasSorts = []
        , sentenceAliasResultSort = sort
        , sentenceAliasAttributes = Attributes attributes
        }

sentenceSymbolWithAttributes
    :: SymbolName
    -> [SortVariable level]
    -> Sort level
    -> [UnifiedPattern]
    -> KoreSentenceSymbol level
sentenceSymbolWithAttributes (SymbolName name) params sort attributes =
    SentenceSymbol
        { sentenceSymbolSymbol = Symbol
            { symbolConstructor = Id name
            , symbolParams = params
            }
        , sentenceSymbolSorts = []
        , sentenceSymbolResultSort = sort
        , sentenceSymbolAttributes = Attributes attributes
        }

metaSymbolSentenceWithSortParameters
    :: SymbolName -> Sort Meta -> [SortVariable Meta] -> Sentence
metaSymbolSentenceWithSortParameters
    (SymbolName name) sort parameters
  =
    MetaSentenceSymbolSentence SentenceSymbol
        { sentenceSymbolSymbol = Symbol
            { symbolConstructor = Id name
            , symbolParams = parameters
            }
        , sentenceSymbolSorts = []
        , sentenceSymbolResultSort = sort
        , sentenceSymbolAttributes = Attributes []
        }

symbolSentenceWithSortParameters
    :: SymbolName
    -> SortName
    -> [SortVariable level]
    -> KoreSentenceSymbol level
symbolSentenceWithSortParameters
    (SymbolName name) (SortName sort) parameters
  =
    SentenceSymbol
        { sentenceSymbolSymbol = Symbol
            { symbolConstructor = Id name
            , symbolParams = parameters
            }
        , sentenceSymbolSorts = []
        , sentenceSymbolResultSort =
            SortActualSort SortActual
                { sortActualName = Id sort
                , sortActualSorts = []
                }
        , sentenceSymbolAttributes = Attributes []
        }

axiomSentenceWithSortParameters
    :: UnifiedPattern -> [UnifiedSortVariable] -> Sentence
axiomSentenceWithSortParameters unifiedPattern parameters =
    SentenceAxiomSentence SentenceAxiom
        { sentenceAxiomParameters = parameters
        , sentenceAxiomPattern = unifiedPattern
        , sentenceAxiomAttributes = Attributes []
        }

axiomSentenceWithAttributes
    :: [UnifiedSortVariable] -> UnifiedPattern -> [UnifiedPattern] -> Sentence
axiomSentenceWithAttributes parameters unifiedPattern attributes =
    SentenceAxiomSentence SentenceAxiom
        { sentenceAxiomParameters = parameters
        , sentenceAxiomPattern = unifiedPattern
        , sentenceAxiomAttributes = Attributes attributes
        }

sentenceAliasWithResultSort
    :: AliasName
    -> Sort level
    -> [SortVariable level]
    -> KoreSentenceAlias level
sentenceAliasWithResultSort
    (AliasName name) sort parameters
  =
    SentenceAlias
        { sentenceAliasAlias = Alias
            { aliasConstructor = Id name
            , aliasParams = parameters
            }
        , sentenceAliasSorts = []
        , sentenceAliasResultSort = sort
        , sentenceAliasAttributes = Attributes []
        }

symbolSentenceWithResultSort
    :: MetaOrObject level
    => SymbolName -> Sort level -> [SortVariable level] -> Sentence
symbolSentenceWithResultSort
    (SymbolName name) sort parameters
  =
    asSentenceSymbolSentence SentenceSymbol
        { sentenceSymbolSymbol = Symbol
            { symbolConstructor = Id name
            , symbolParams = parameters
            }
        , sentenceSymbolSorts = []
        , sentenceSymbolResultSort = sort
        , sentenceSymbolAttributes = Attributes []
        }

objectSymbolSentenceWithArguments
    :: SymbolName -> Sort Object -> [Sort Object] -> Sentence
objectSymbolSentenceWithArguments = symbolSentenceWithArguments

symbolSentenceWithArguments
    :: MetaOrObject level
    => SymbolName -> Sort level -> [Sort level] -> Sentence
symbolSentenceWithArguments
    (SymbolName name) sort operandSorts
  =
    asSentenceSymbolSentence SentenceSymbol
        { sentenceSymbolSymbol = Symbol
            { symbolConstructor = Id name
            , symbolParams = []
            }
        , sentenceSymbolSorts = operandSorts
        , sentenceSymbolResultSort = sort
        , sentenceSymbolAttributes = Attributes []
        }

objectAliasSentenceWithArguments
    :: AliasName -> Sort Object -> [Sort Object] -> Sentence
objectAliasSentenceWithArguments = aliasSentenceWithArguments

aliasSentenceWithArguments
    :: MetaOrObject level => AliasName -> Sort level -> [Sort level] -> Sentence
aliasSentenceWithArguments
    (AliasName name) sort operandSorts
  =
    asSentenceAliasSentence SentenceAlias
        { sentenceAliasAlias = Alias
            { aliasConstructor = Id name
            , aliasParams = []
            }
        , sentenceAliasSorts = operandSorts
        , sentenceAliasResultSort = sort
        , sentenceAliasAttributes = Attributes []
        }

simpleSortActual :: SortName -> SortActual level
simpleSortActual (SortName sort) =
    SortActual
        { sortActualName = Id sort
        , sortActualSorts = []
        }

simpleSort :: SortName -> Sort level
simpleSort sortName =
    SortActualSort (simpleSortActual sortName)

objectVariableSort :: SortVariableName -> Sort Object
objectVariableSort = sortVariableSort

sortVariableSort :: SortVariableName -> Sort level
sortVariableSort (SortVariableName sort) =
    SortVariableSort (SortVariable (Id sort))

sortVariable :: level -> SortVariableName -> SortVariable level
sortVariable _ (SortVariableName name) = SortVariable (Id name)

unifiedSortVariable
    :: MetaOrObject level => level -> SortVariableName -> UnifiedSortVariable
unifiedSortVariable x name =
    asUnified (sortVariable x name)

stringUnifiedPattern :: String -> UnifiedPattern
stringUnifiedPattern s =
    MetaPattern (StringLiteralPattern (StringLiteral s))

variable :: VariableName -> Sort level -> Variable level
variable (VariableName name) sort =
    Variable
        { variableName = Id name
        , variableSort = sort
        }

unifiedVariable
    :: MetaOrObject level
    => VariableName -> Sort level -> UnifiedVariable Variable
unifiedVariable name sort =
    asUnified (variable name sort)

variablePattern :: VariableName -> Sort level -> Pattern level Variable p
variablePattern name sort =
    VariablePattern (variable name sort)

unifiedVariablePattern
    :: MetaOrObject level => VariableName -> Sort level -> UnifiedPattern
unifiedVariablePattern name sort =
    asUnifiedPattern (variablePattern name sort)

simpleExistsPattern
    :: MetaOrObject level
    => Variable level -> Sort level -> Pattern level Variable UnifiedPattern
simpleExistsPattern quantifiedVariable resultSort =
    ExistsPattern Exists
        { existsSort = resultSort
        , existsVariable = quantifiedVariable
        , existsChild = asUnifiedPattern (VariablePattern quantifiedVariable)
        }

simpleExistsUnifiedPattern
    :: MetaOrObject level => VariableName -> Sort level -> UnifiedPattern
simpleExistsUnifiedPattern name sort =
    asUnifiedPattern
        ( simpleExistsPattern
            (variable name sort)
            sort
        )

simpleExistsObjectUnifiedPattern
    :: VariableName -> Sort Object -> UnifiedPattern
simpleExistsObjectUnifiedPattern = simpleExistsUnifiedPattern

simpleExistsUnifiedPatternWithType
    :: MetaOrObject level
    => level -> VariableName -> Sort level -> UnifiedPattern
simpleExistsUnifiedPatternWithType _ = simpleExistsUnifiedPattern

simpleExistsEqualsUnifiedPattern
    :: MetaOrObject level
    => VariableName
    -> OperandSort level
    -> ResultSort level
    -> UnifiedPattern
simpleExistsEqualsUnifiedPattern
    name
    (OperandSort operandSort)
    (ResultSort resultSort)
  =
    asUnifiedPattern
        (ExistsPattern Exists
            { existsSort = resultSort
            , existsVariable = variable name operandSort
            , existsChild = asUnifiedPattern
                (EqualsPattern Equals
                    { equalsOperandSort = operandSort
                    , equalsResultSort = resultSort
                    , equalsFirst =
                        unifiedVariablePattern name operandSort
                    , equalsSecond =
                        unifiedVariablePattern name operandSort
                    }
                )
            }
        )

applicationObjectUnifiedPatternWithChildren
    :: SymbolName -> [UnifiedPattern] -> UnifiedPattern
applicationObjectUnifiedPatternWithChildren name unifiedPatterns =
    ObjectPattern (applicationPatternWithChildren name unifiedPatterns)

applicationPatternWithChildren
    :: SymbolName -> [UnifiedPattern] -> Pattern level v UnifiedPattern
applicationPatternWithChildren (SymbolName name) unifiedPatterns =
    ApplicationPattern Application
        { applicationSymbolOrAlias = SymbolOrAlias
            { symbolOrAliasConstructor = Id name
            , symbolOrAliasParams = []
            }
        , applicationChildren = unifiedPatterns
        }

applicationUnifiedPatternWithParams
    :: MetaOrObject level => SymbolName -> [Sort level] -> UnifiedPattern
applicationUnifiedPatternWithParams (SymbolName name) params =
    asUnifiedPattern
        (ApplicationPattern Application
            { applicationSymbolOrAlias = SymbolOrAlias
                { symbolOrAliasConstructor = Id name
                , symbolOrAliasParams = params
                }
            , applicationChildren = []
            }
        )
