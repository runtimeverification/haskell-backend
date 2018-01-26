module Data.Kore.ASTVerifier.DefinitionVerifierTestHelpers where

import           Test.Tasty       (TestTree, testGroup)
import           Test.Tasty.HUnit (assertEqual, assertFailure, testCase)


import           Data.Kore.AST
import           Data.Kore.ASTPrettyPrint
import           Data.Kore.ASTVerifier.DefinitionVerifier
import           Data.Kore.ASTVerifier.Error
import           Data.Kore.Error
import           Data.Kore.Unparser.Unparse

newtype ExpectedErrorMessage = ExpectedErrorMessage String
newtype ErrorStack = ErrorStack [String]

data TestData = TestData
    { testDataDescription :: !String
    , testDataError :: !(Error VerifyError)
    , testDataDefinition :: !Definition
    }

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
newtype OperandSort a = OperandSort (Sort a)
newtype ResultSort a = ResultSort (Sort a)
newtype DeclaredSort a = DeclaredSort (Sort a)
newtype TestedPatternSort a = TestedPatternSort (Sort a)
newtype SortVariablesThatMustBeDeclared a =
    SortVariablesThatMustBeDeclared [SortVariable a]

simpleDefinitionFromSentences :: ModuleName -> [Sentence] -> Definition
simpleDefinitionFromSentences name sentences =
    Definition
        { definitionAttributes = Attributes []
        , definitionModules = Module
            { moduleName = name
            , moduleSentences = sentences
            , moduleAttributes = Attributes []
            }
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

simpleAliasSentence :: AliasName -> SortName -> SentenceAlias a
simpleAliasSentence (AliasName name) (SortName sort) =
    SentenceAlias
        { sentenceAliasAlias = Alias
            { aliasConstructor = Id name
            , aliasParams = []
            }
        , sentenceAliasSorts = []
        , sentenceAliasReturnSort =
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

simpleSymbolSentence :: SymbolName -> SortName -> SentenceSymbol a
simpleSymbolSentence (SymbolName name) (SortName sort) =
    SentenceSymbol
        { sentenceSymbolSymbol = Symbol
            { symbolConstructor = Id name
            , symbolParams = []
            }
        , sentenceSymbolSorts = []
        , sentenceSymbolReturnSort =
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

sortSentenceWithSortParameters :: SortName -> [SortVariable Object] -> Sentence
sortSentenceWithSortParameters (SortName name) parameters =
    SentenceSortSentence SentenceSort
        { sentenceSortName = Id name
        , sentenceSortParameters = parameters
        , sentenceSortAttributes = Attributes []
        }

aliasSentenceWithSort :: IsMeta a => AliasName -> Sort a -> Sentence
aliasSentenceWithSort (AliasName name) sort =
    asSentenceAliasSentence SentenceAlias
        { sentenceAliasAlias = Alias
            { aliasConstructor = Id name
            , aliasParams = []
            }
        , sentenceAliasSorts = []
        , sentenceAliasReturnSort = sort
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
        , sentenceAliasReturnSort = sort
        , sentenceAliasAttributes = Attributes []
        }

aliasSentenceWithSortParameters
    :: AliasName -> SortName -> [SortVariable a] -> SentenceAlias a
aliasSentenceWithSortParameters
    (AliasName name) (SortName sort) parameters
  =
    SentenceAlias
        { sentenceAliasAlias = Alias
            { aliasConstructor = Id name
            , aliasParams = parameters
            }
        , sentenceAliasSorts = []
        , sentenceAliasReturnSort =
            SortActualSort SortActual
                { sortActualName = Id sort
                , sortActualSorts = []
                }
        , sentenceAliasAttributes = Attributes []
        }

sentenceAliasWithSortArgument
    :: AliasName -> Sort a -> Sort a -> [SortVariable a] -> SentenceAlias a
sentenceAliasWithSortArgument
    (AliasName name) sortArgument resultSort parameters
  =
    SentenceAlias
        { sentenceAliasAlias = Alias
            { aliasConstructor = Id name
            , aliasParams = parameters
            }
        , sentenceAliasSorts = [sortArgument]
        , sentenceAliasReturnSort = resultSort
        , sentenceAliasAttributes = Attributes []
        }

sentenceAliasWithAttributes
    :: AliasName
    -> [SortVariable a]
    -> Sort a
    -> [UnifiedPattern]
    -> SentenceAlias a
sentenceAliasWithAttributes (AliasName name) params sort attributes =
    SentenceAlias
        { sentenceAliasAlias = Alias
            { aliasConstructor = Id name
            , aliasParams = params
            }
        , sentenceAliasSorts = []
        , sentenceAliasReturnSort = sort
        , sentenceAliasAttributes = Attributes attributes
        }

sentenceSymbolWithAttributes
    :: SymbolName
    -> [SortVariable a]
    -> Sort a
    -> [UnifiedPattern]
    -> SentenceSymbol a
sentenceSymbolWithAttributes (SymbolName name) params sort attributes =
    SentenceSymbol
        { sentenceSymbolSymbol = Symbol
            { symbolConstructor = Id name
            , symbolParams = params
            }
        , sentenceSymbolSorts = []
        , sentenceSymbolReturnSort = sort
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
        , sentenceSymbolReturnSort = sort
        , sentenceSymbolAttributes = Attributes []
        }

symbolSentenceWithSortParameters
    :: SymbolName -> SortName -> [SortVariable a] -> SentenceSymbol a
symbolSentenceWithSortParameters
    (SymbolName name) (SortName sort) parameters
  =
    SentenceSymbol
        { sentenceSymbolSymbol = Symbol
            { symbolConstructor = Id name
            , symbolParams = parameters
            }
        , sentenceSymbolSorts = []
        , sentenceSymbolReturnSort =
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

sentenceAliasWithReturnSort
    :: AliasName -> Sort a -> [SortVariable a] -> SentenceAlias a
sentenceAliasWithReturnSort
    (AliasName name) sort parameters
  =
    SentenceAlias
        { sentenceAliasAlias = Alias
            { aliasConstructor = Id name
            , aliasParams = parameters
            }
        , sentenceAliasSorts = []
        , sentenceAliasReturnSort = sort
        , sentenceAliasAttributes = Attributes []
        }

symbolSentenceWithReturnSort
    :: IsMeta a => SymbolName -> Sort a -> [SortVariable a] -> Sentence
symbolSentenceWithReturnSort
    (SymbolName name) sort parameters
  =
    asSentenceSymbolSentence SentenceSymbol
        { sentenceSymbolSymbol = Symbol
            { symbolConstructor = Id name
            , symbolParams = parameters
            }
        , sentenceSymbolSorts = []
        , sentenceSymbolReturnSort = sort
        , sentenceSymbolAttributes = Attributes []
        }

objectSymbolSentenceWithArguments
    :: SymbolName -> Sort Object -> [Sort Object] -> Sentence
objectSymbolSentenceWithArguments = symbolSentenceWithArguments

symbolSentenceWithArguments
    :: IsMeta a => SymbolName -> Sort a -> [Sort a] -> Sentence
symbolSentenceWithArguments
    (SymbolName name) sort operandSorts
  =
    asSentenceSymbolSentence SentenceSymbol
        { sentenceSymbolSymbol = Symbol
            { symbolConstructor = Id name
            , symbolParams = []
            }
        , sentenceSymbolSorts = operandSorts
        , sentenceSymbolReturnSort = sort
        , sentenceSymbolAttributes = Attributes []
        }

objectAliasSentenceWithArguments
    :: AliasName -> Sort Object -> [Sort Object] -> Sentence
objectAliasSentenceWithArguments = aliasSentenceWithArguments

aliasSentenceWithArguments
    :: IsMeta a => AliasName -> Sort a -> [Sort a] -> Sentence
aliasSentenceWithArguments
    (AliasName name) sort operandSorts
  =
    asSentenceAliasSentence SentenceAlias
        { sentenceAliasAlias = Alias
            { aliasConstructor = Id name
            , aliasParams = []
            }
        , sentenceAliasSorts = operandSorts
        , sentenceAliasReturnSort = sort
        , sentenceAliasAttributes = Attributes []
        }

simpleSortActual :: SortName -> SortActual a
simpleSortActual (SortName sort) =
    SortActual
        { sortActualName = Id sort
        , sortActualSorts = []
        }

simpleSort :: SortName -> Sort a
simpleSort sortName =
    SortActualSort (simpleSortActual sortName)

objectVariableSort :: SortVariableName -> Sort Object
objectVariableSort = sortVariableSort

sortVariableSort :: SortVariableName -> Sort a
sortVariableSort (SortVariableName sort) =
    SortVariableSort (SortVariable (Id sort))

sortVariable :: a -> SortVariableName -> SortVariable a
sortVariable _ (SortVariableName name) = SortVariable (Id name)

unifiedSortVariable :: IsMeta a => a -> SortVariableName -> UnifiedSortVariable
unifiedSortVariable x name =
    asUnifiedSortVariable (sortVariable x name)

stringUnifiedPattern :: String -> UnifiedPattern
stringUnifiedPattern s =
    MetaPattern (StringLiteralPattern (StringLiteral s))

variable :: VariableName -> Sort a -> Variable a
variable (VariableName name) sort =
    Variable
        { variableName = Id name
        , variableSort = sort
        }

unifiedVariable :: IsMeta a => VariableName -> Sort a -> UnifiedVariable
unifiedVariable name sort =
    asUnifiedVariable (variable name sort)

variablePattern :: VariableName -> Sort a -> Pattern a
variablePattern name sort =
    VariablePattern (variable name sort)

unifiedVariablePattern :: IsMeta a => VariableName -> Sort a -> UnifiedPattern
unifiedVariablePattern name sort =
    asUnifiedPattern (variablePattern name sort)

simpleExistsPattern :: IsMeta a => Variable a -> Sort a -> Pattern a
simpleExistsPattern quantifiedVariable returnSort =
    ExistsPattern Exists
        { existsSort = returnSort
        , existsVariable = asUnifiedVariable quantifiedVariable
        , existsPattern = asUnifiedPattern (VariablePattern quantifiedVariable)
        }

simpleExistsUnifiedPattern
    :: IsMeta a => VariableName -> Sort a -> UnifiedPattern
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
    :: IsMeta a => a -> VariableName -> Sort a -> UnifiedPattern
simpleExistsUnifiedPatternWithType _ = simpleExistsUnifiedPattern

simpleExistsEqualsUnifiedPattern
    :: IsMeta a
    => VariableName
    -> OperandSort a
    -> ResultSort a
    -> UnifiedPattern
simpleExistsEqualsUnifiedPattern
    name
    (OperandSort operandSort)
    (ResultSort resultSort)
  =
    asUnifiedPattern
        (ExistsPattern Exists
            { existsSort = resultSort
            , existsVariable = unifiedVariable name operandSort
            , existsPattern = asUnifiedPattern
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

applicationPatternWithChildren :: SymbolName -> [UnifiedPattern] -> Pattern a
applicationPatternWithChildren (SymbolName name) unifiedPatterns =
    ApplicationPattern Application
        { applicationSymbolOrAlias = SymbolOrAlias
            { symbolOrAliasConstructor = Id name
            , symbolOrAliasParams = []
            }
        , applicationPatterns = unifiedPatterns
        }

applicationUnifiedPatternWithParams
    :: IsMeta a => SymbolName -> [Sort a] -> UnifiedPattern
applicationUnifiedPatternWithParams (SymbolName name) params =
    asUnifiedPattern
        (ApplicationPattern Application
            { applicationSymbolOrAlias = SymbolOrAlias
                { symbolOrAliasConstructor = Id name
                , symbolOrAliasParams = params
                }
            , applicationPatterns = []
            }
        )
