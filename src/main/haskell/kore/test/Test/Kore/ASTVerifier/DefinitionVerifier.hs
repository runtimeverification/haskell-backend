module Test.Kore.ASTVerifier.DefinitionVerifier where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
       ( HasCallStack, assertEqual, assertFailure, testCase )

import qualified Data.Set as Set
import           Data.Text
                 ( Text )

import           Kore.AST.Kore
import           Kore.AST.Sentence
import           Kore.AST.Valid
import           Kore.ASTPrettyPrint
import           Kore.ASTVerifier.DefinitionVerifier
import           Kore.ASTVerifier.Error
import qualified Kore.Attribute.Null as Attribute
import qualified Kore.Builtin as Builtin
import qualified Kore.Domain.Builtin as Domain
import           Kore.Error
import           Kore.Implicit.ImplicitSorts
import           Kore.Step.Pattern
import           Kore.Unparser
                 ( unparseToString )

import Test.Kore

newtype ExpectedErrorMessage = ExpectedErrorMessage String
newtype ErrorStack = ErrorStack [String]

data TestData = TestData
    { testDataDescription :: !String
    , testDataError       :: !(Error VerifyError)
    , testDataDefinition  :: !VerifiedKoreDefinition
    }

addPrefixToDescription :: String -> [TestData] -> [TestData]
addPrefixToDescription prefix =
    map
        (\t -> t {testDataDescription = prefix ++ testDataDescription t})

failureTestDataGroup
    :: HasCallStack
    => String -> ExpectedErrorMessage -> ErrorStack -> [TestData] -> TestTree
failureTestDataGroup description errorMessage errorStack testData =
    testGroup
        description
        (map (failureTestData errorMessage errorStack) testData)

failureTestData
    :: HasCallStack
    => ExpectedErrorMessage -> ErrorStack -> TestData -> TestTree
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

successTestDataGroup :: HasCallStack => String -> [TestData] -> TestTree
successTestDataGroup description testDatas =
    testGroup description (map successTestData testDatas)

successTestData :: HasCallStack => TestData -> TestTree
successTestData testData =
    expectSuccess (testDataDescription testData) (testDataDefinition testData)

expectSuccess
    :: HasCallStack
    => String
    -> Definition
        (UnifiedSentence
            UnifiedSortVariable
            (KorePattern
                Domain.Builtin
                Variable
                erased
            )
        )
    -> TestTree
expectSuccess description (fmap eraseUnifiedSentenceAnnotations -> definition) =
    testCase
        description
        (assertEqual
            (  "Expecting verification success! Definition:\n"
            ++ printDefinition definition
            )
            verifySuccess
            (verifyDefinition
                attributesVerificationForTests
                Builtin.koreVerifiers
                definition
            )
        )

expectFailureWithError
    :: HasCallStack
    => String
    -> Error VerifyError
    -> VerifiedKoreDefinition
    -> TestTree
expectFailureWithError description expectedError definition =
    testCase
        description
        (case
            verifyDefinition
                attributesVerificationForTests
                Builtin.koreVerifiers
                definition'
          of
            Right _ ->
                assertFailure
                    (  "Expecting verification failure! Definition:\n"
                    ++ printDefinition definition'
                    )
            Left actualError ->
                assertEqual
                    ( "Expecting a certain error! Definition:\n"
                    ++ printDefinition definition'
                    )
                    expectedError actualError
        )
  where
    definition' = eraseUnifiedSentenceAnnotations <$> definition

attributesVerificationForTests
    :: AttributesVerification Attribute.Null Attribute.Null
attributesVerificationForTests = defaultNullAttributesVerification

printDefinition :: KoreDefinition -> String
printDefinition definition =
    prettyPrintToString definition
    ++ "\n----------------------\n"
    ++ unparseToString definition
    ++ "\n----------------------"

-------------------------------------------------------------

newtype AliasName = AliasName Text
newtype SymbolName = SymbolName Text
newtype SortName = SortName Text
newtype SortVariableName = SortVariableName Text
newtype VariableName = VariableName Text
newtype NamePrefix = NamePrefix Text
newtype OperandSort level = OperandSort (Sort level)
newtype ResultSort level = ResultSort (Sort level)
newtype DeclaredSort level = DeclaredSort (Sort level)
newtype TestedPatternSort level = TestedPatternSort (Sort level)
newtype SortVariablesThatMustBeDeclared level =
    SortVariablesThatMustBeDeclared [SortVariable level]

simpleDefinitionFromSentences
    :: ModuleName
    -> [VerifiedKoreSentence]
    -> VerifiedKoreDefinition
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

-- TODO: simple meta sort sentence?
simpleSortSentence :: SortName -> VerifiedKoreSentence
simpleSortSentence (SortName name) =
    asSentence
        (SentenceSort
            { sentenceSortName = testId name :: Id Object
            , sentenceSortParameters = []
            , sentenceSortAttributes = Attributes []
            }
            :: VerifiedKoreSentenceSort Object
        )

simpleMetaAliasSentence :: AliasName -> SortName -> VerifiedKoreSentence
simpleMetaAliasSentence alias sort =
    asSentence (simpleAliasSentence @Meta alias sort r)
  where
    r = toKorePattern $ mkTop (simpleSort sort :: Sort Meta)

simpleObjectAliasSentence :: AliasName -> SortName -> VerifiedKoreSentence
simpleObjectAliasSentence alias sort =
   asSentence (simpleAliasSentence @Object alias sort r)
  where
    r = toKorePattern $ mkTop (simpleSort sort :: Sort Object)

simpleAliasSentence
    :: AliasName
    -> SortName
    -> VerifiedKorePattern
    -> VerifiedKoreSentenceAlias level
simpleAliasSentence (AliasName name) (SortName sort) r =
    SentenceAlias
        { sentenceAliasAlias = Alias
            { aliasConstructor = testId name
            , aliasParams = []
            }
        , sentenceAliasSorts = []
        , sentenceAliasResultSort =
            SortActualSort SortActual
                { sortActualName = testId sort
                , sortActualSorts = []
                }
        , sentenceAliasLeftPattern =
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = testId name
                        , symbolOrAliasParams = []
                        }
                , applicationChildren = []
                }
        , sentenceAliasRightPattern = r
        , sentenceAliasAttributes = Attributes []
        }

simpleMetaSymbolSentence :: SymbolName -> SortName -> VerifiedKoreSentence
simpleMetaSymbolSentence name sort =
    asSentence (simpleSymbolSentence @Meta name sort)

simpleObjectSymbolSentence :: SymbolName -> SortName -> VerifiedKoreSentence
simpleObjectSymbolSentence name sort =
    asSentence (simpleSymbolSentence @Object name sort)

simpleSymbolSentence
    :: SymbolName
    -> SortName
    -> VerifiedKoreSentenceSymbol level
simpleSymbolSentence (SymbolName name) (SortName sort) =
    SentenceSymbol
        { sentenceSymbolSymbol = Symbol
            { symbolConstructor = testId name
            , symbolParams = []
            }
        , sentenceSymbolSorts = []
        , sentenceSymbolResultSort =
            SortActualSort SortActual
                { sortActualName = testId sort
                , sortActualSorts = []
                }
        , sentenceSymbolAttributes = Attributes []
        }

simpleAxiomSentence :: VerifiedKorePattern -> VerifiedKoreSentence
simpleAxiomSentence unifiedPattern =
    asKoreAxiomSentence
        (SentenceAxiom
            { sentenceAxiomParameters = []
            , sentenceAxiomPattern = unifiedPattern
            , sentenceAxiomAttributes = Attributes []
            }
            :: VerifiedKoreSentenceAxiom
        )

importSentence :: ModuleName -> VerifiedKoreSentence
importSentence name =
    asSentence
        (SentenceImport
            { sentenceImportModuleName = name
            , sentenceImportAttributes = Attributes []
            }
            :: VerifiedKoreSentenceImport
        )

sortSentenceWithSortParameters
    :: SortName -> [SortVariable Object] -> VerifiedKoreSentence
sortSentenceWithSortParameters (SortName name) parameters =
    asSentence
        (SentenceSort
            { sentenceSortName = testId name
            , sentenceSortParameters = parameters
            , sentenceSortAttributes = Attributes []
            }
            :: VerifiedKoreSentenceSort Object
        )

aliasSentenceWithSort
    :: AliasName -> Sort Meta -> VerifiedKoreSentence
aliasSentenceWithSort (AliasName name) sort =
    constructUnifiedSentence SentenceAliasSentence $
        SentenceAlias
            { sentenceAliasAlias = Alias
                { aliasConstructor = testId name
                , aliasParams = []
                }
            , sentenceAliasSorts = []
            , sentenceAliasResultSort = sort
            , sentenceAliasLeftPattern =
                Application
                    { applicationSymbolOrAlias =
                        SymbolOrAlias
                            { symbolOrAliasConstructor = testId name
                            , symbolOrAliasParams = []
                            }
                    , applicationChildren = []
                    }
            , sentenceAliasRightPattern =
                toKorePattern $ mkTop patternMetaSort
            , sentenceAliasAttributes =
                Attributes [] :: Attributes
            }

metaAliasSentenceWithSortParameters
    :: AliasName -> Sort Meta -> [SortVariable Meta] -> VerifiedKoreSentence
metaAliasSentenceWithSortParameters
    (AliasName name) sort parameters
  =
    asSentence
        (SentenceAlias
            { sentenceAliasAlias = Alias
                { aliasConstructor = testId name
                , aliasParams = parameters
                }
            , sentenceAliasSorts = []
            , sentenceAliasResultSort = sort
            , sentenceAliasLeftPattern =
                Application
                    { applicationSymbolOrAlias =
                        SymbolOrAlias
                            { symbolOrAliasConstructor = testId name
                            , symbolOrAliasParams =
                                SortVariableSort <$> parameters
                            }
                    , applicationChildren = []
                    }
            , sentenceAliasRightPattern =
                toKorePattern $ mkTop sort
            , sentenceAliasAttributes = Attributes []
            }
            :: VerifiedKoreSentenceAlias Meta
        )


aliasSentenceWithSortParameters
    :: AliasName
    -> SortName
    -> [SortVariable level]
    -> VerifiedKorePattern
    -> VerifiedKoreSentenceAlias level
aliasSentenceWithSortParameters (AliasName name) (SortName sort) parameters r =
    SentenceAlias
        { sentenceAliasAlias = Alias
            { aliasConstructor = testId name
            , aliasParams = parameters
            }
        , sentenceAliasSorts = []
        , sentenceAliasResultSort =
            SortActualSort SortActual
                { sortActualName = testId sort
                , sortActualSorts = []
                }
        , sentenceAliasLeftPattern =
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = testId name
                        , symbolOrAliasParams = SortVariableSort <$> parameters
                        }
                , applicationChildren = []
                }
        , sentenceAliasRightPattern = r
        , sentenceAliasAttributes = Attributes []
        }

sentenceAliasWithSortArgument
    :: MetaOrObject level
    => AliasName
    -> Sort level
    -> Sort level
    -> [SortVariable level]
    -> VerifiedKorePattern
    -> VerifiedKoreSentenceAlias level
sentenceAliasWithSortArgument
    (AliasName name)
    sortArgument
    resultSort
    parameters
    r
  =
    SentenceAlias
        { sentenceAliasAlias = Alias
            { aliasConstructor = testId name
            , aliasParams = parameters
            }
        , sentenceAliasSorts = [sortArgument]
        , sentenceAliasResultSort = resultSort
        , sentenceAliasLeftPattern =
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = testId name
                        , symbolOrAliasParams =
                            SortVariableSort <$> parameters
                        }
                , applicationChildren =
                    [ Variable
                        { variableName = testId "x"
                        , variableSort = sortArgument
                        }
                    ]
                }
        , sentenceAliasRightPattern = r
        , sentenceAliasAttributes = Attributes []
        }

sentenceAliasWithAttributes
    :: AliasName
    -> [SortVariable level]
    -> Sort level
    -> [CommonKorePattern]
    -> Application level (Variable level)
    -> CommonKorePattern
    -> KoreSentenceAlias level
sentenceAliasWithAttributes (AliasName name) params sort attributes l r =
    SentenceAlias
        { sentenceAliasAlias = Alias
            { aliasConstructor = testId name
            , aliasParams = params
            }
        , sentenceAliasSorts = []
        , sentenceAliasResultSort = sort
        , sentenceAliasLeftPattern = l
        , sentenceAliasRightPattern = r
        , sentenceAliasAttributes = Attributes attributes
        }

sentenceSymbolWithAttributes
    :: SymbolName
    -> [SortVariable level]
    -> Sort level
    -> [CommonKorePattern]
    -> KoreSentenceSymbol level
sentenceSymbolWithAttributes (SymbolName name) params sort attributes =
    SentenceSymbol
        { sentenceSymbolSymbol = Symbol
            { symbolConstructor = testId name
            , symbolParams = params
            }
        , sentenceSymbolSorts = []
        , sentenceSymbolResultSort = sort
        , sentenceSymbolAttributes = Attributes attributes
        }

metaSymbolSentenceWithSortParameters
    :: SymbolName -> Sort Meta -> [SortVariable Meta] -> VerifiedKoreSentence
metaSymbolSentenceWithSortParameters
    (SymbolName name) sort parameters
  =
    asSentence
        (SentenceSymbol
            { sentenceSymbolSymbol = Symbol
                { symbolConstructor = testId name
                , symbolParams = parameters
                }
            , sentenceSymbolSorts = []
            , sentenceSymbolResultSort = sort
            , sentenceSymbolAttributes = Attributes []
            }
            :: VerifiedKoreSentenceSymbol Meta
        )

symbolSentenceWithSortParameters
    :: SymbolName
    -> SortName
    -> [SortVariable level]
    -> VerifiedKoreSentenceSymbol level
symbolSentenceWithSortParameters
    (SymbolName name) (SortName sort) parameters
  =
    SentenceSymbol
        { sentenceSymbolSymbol = Symbol
            { symbolConstructor = testId name
            , symbolParams = parameters
            }
        , sentenceSymbolSorts = []
        , sentenceSymbolResultSort =
            SortActualSort SortActual
                { sortActualName = testId sort
                , sortActualSorts = []
                }
        , sentenceSymbolAttributes = Attributes []
        }

axiomSentenceWithSortParameters
    :: VerifiedKorePattern -> [UnifiedSortVariable] -> VerifiedKoreSentence
axiomSentenceWithSortParameters unifiedPattern parameters =
    asKoreAxiomSentence
        (SentenceAxiom
            { sentenceAxiomParameters = parameters
            , sentenceAxiomPattern = unifiedPattern
            , sentenceAxiomAttributes = Attributes []
            }
            :: VerifiedKoreSentenceAxiom
        )

axiomSentenceWithAttributes
    :: [UnifiedSortVariable]
    -> CommonKorePattern
    -> [CommonKorePattern]
    -> KoreSentence
axiomSentenceWithAttributes parameters unifiedPattern attributes =
    asKoreAxiomSentence
        (SentenceAxiom
            { sentenceAxiomParameters = parameters
            , sentenceAxiomPattern = unifiedPattern
            , sentenceAxiomAttributes = Attributes attributes
            }::KoreSentenceAxiom
        )

sentenceAliasWithResultSort
    :: AliasName
    -> Sort level
    -> [SortVariable level]
    -> VerifiedKorePattern
    -> VerifiedKoreSentenceAlias level
sentenceAliasWithResultSort (AliasName name) sort parameters r =
    SentenceAlias
        { sentenceAliasAlias = Alias
            { aliasConstructor = testId name
            , aliasParams = parameters
            }
        , sentenceAliasSorts = []
        , sentenceAliasResultSort = sort
        , sentenceAliasLeftPattern =
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = testId name
                        , symbolOrAliasParams =
                            SortVariableSort <$> parameters
                        }
                , applicationChildren = []
                }
        , sentenceAliasRightPattern = r
        , sentenceAliasAttributes = Attributes []
        }

symbolSentenceWithResultSort
    :: MetaOrObject level
    => SymbolName -> Sort level -> [SortVariable level] -> VerifiedKoreSentence
symbolSentenceWithResultSort
    (SymbolName name) sort parameters
  = constructUnifiedSentence SentenceSymbolSentence $
        SentenceSymbol
            { sentenceSymbolSymbol = Symbol
                { symbolConstructor = testId name
                , symbolParams = parameters
                }
            , sentenceSymbolSorts = []
            , sentenceSymbolResultSort = sort
            , sentenceSymbolAttributes =
                Attributes [] :: Attributes
            }

objectSymbolSentenceWithArguments
    :: SymbolName -> Sort Object -> [Sort Object] -> VerifiedKoreSentence
objectSymbolSentenceWithArguments = symbolSentenceWithArguments

symbolSentenceWithArguments
    :: MetaOrObject level
    => SymbolName -> Sort level -> [Sort level] -> VerifiedKoreSentence
symbolSentenceWithArguments name
  = symbolSentenceWithParametersAndArguments name []

objectSymbolSentenceWithParametersAndArguments
    :: SymbolName
    -> [SortVariable Object]
    -> Sort Object
    -> [Sort Object]
    -> VerifiedKoreSentence
objectSymbolSentenceWithParametersAndArguments
  = symbolSentenceWithParametersAndArguments

symbolSentenceWithParametersAndArguments
    :: MetaOrObject level
    => SymbolName
    -> [SortVariable level]
    -> Sort level
    -> [Sort level]
    -> VerifiedKoreSentence
symbolSentenceWithParametersAndArguments
    (SymbolName name) params sort operandSorts
  = constructUnifiedSentence SentenceSymbolSentence $
        SentenceSymbol
            { sentenceSymbolSymbol = Symbol
                { symbolConstructor = testId name
                , symbolParams = params
                }
            , sentenceSymbolSorts = operandSorts
            , sentenceSymbolResultSort = sort
            , sentenceSymbolAttributes =
                Attributes [] :: Attributes
            }

objectAliasSentenceWithArguments
    :: AliasName -> Sort Object -> [Variable Object] -> VerifiedKoreSentence
objectAliasSentenceWithArguments a b c =
    aliasSentenceWithArguments
        a
        b
        c
        (asKorePattern $ valid :< top')
  where
    top' = TopPattern Top { topSort = b }
    valid = Valid { patternSort = b, freeVariables = Set.empty }

aliasSentenceWithArguments
    :: MetaOrObject level
    => AliasName
    -> Sort level
    -> [Variable level]
    -> VerifiedKorePattern
    -> VerifiedKoreSentence
aliasSentenceWithArguments (AliasName name) sort operands r =
    constructUnifiedSentence SentenceAliasSentence $
        SentenceAlias
            { sentenceAliasAlias = Alias
                { aliasConstructor = testId name
                , aliasParams = []
                }
            , sentenceAliasSorts =
                variableSort <$> operands
            , sentenceAliasResultSort = sort
            , sentenceAliasLeftPattern =
                Application
                    { applicationSymbolOrAlias =
                        SymbolOrAlias
                            { symbolOrAliasConstructor = testId name
                            , symbolOrAliasParams = []
                            }
                    , applicationChildren = operands
                    }
            , sentenceAliasRightPattern = r
            , sentenceAliasAttributes = Attributes []
            }

simpleSortActual :: SortName -> SortActual level
simpleSortActual (SortName sort) =
    SortActual
        { sortActualName = testId sort
        , sortActualSorts = []
        }

simpleSort :: SortName -> Sort level
simpleSort sortName =
    SortActualSort (simpleSortActual sortName)

objectVariableSort :: Text -> Sort Object
objectVariableSort name = sortVariableSort name

unifiedSortVariable
    :: forall level . MetaOrObject level
    => level -> SortVariableName -> UnifiedSortVariable
unifiedSortVariable _x (SortVariableName name) =
    asUnified (sortVariable name :: SortVariable level)

stringUnifiedPattern :: Text -> VerifiedKorePattern
stringUnifiedPattern s = toKorePattern (mkStringLiteral s)

variable :: VariableName -> Sort level -> Variable level
variable (VariableName name) sort =
    Variable
        { variableName = testId name
        , variableSort = sort
        }

unifiedVariable
    :: MetaOrObject level
    => VariableName -> Sort level -> Unified Variable
unifiedVariable name sort =
    asUnified (variable name sort)

variablePattern :: VariableName -> Sort level -> Pattern level domain Variable p
variablePattern name sort =
    VariablePattern (variable name sort)

unifiedVariablePattern
    :: MetaOrObject level => VariableName -> Sort level -> VerifiedKorePattern
unifiedVariablePattern name patternSort =
    asKorePattern (valid :< variablePattern name patternSort)
  where
    freeVariables = Set.singleton (asUnified $ variable name patternSort)
    valid = Valid { patternSort, freeVariables }

simpleExistsPattern
    :: MetaOrObject level
    => Variable level
    -> Sort level
    -> Pattern level domain Variable VerifiedKorePattern
simpleExistsPattern quantifiedVariable resultSort =
    ExistsPattern Exists
        { existsSort = resultSort
        , existsVariable = quantifiedVariable
        , existsChild = toKorePattern $ mkVar quantifiedVariable
        }

simpleExistsUnifiedPattern
    :: MetaOrObject level => VariableName -> Sort level -> VerifiedKorePattern
simpleExistsUnifiedPattern name sort =
    asKorePattern $ valid :< simpleExistsPattern (variable name sort) sort
  where
    valid = Valid { patternSort = sort, freeVariables = Set.empty }

simpleExistsObjectUnifiedPattern
    :: VariableName -> Sort Object -> VerifiedKorePattern
simpleExistsObjectUnifiedPattern = simpleExistsUnifiedPattern

simpleExistsUnifiedPatternWithType
    :: MetaOrObject level
    => level -> VariableName -> Sort level -> VerifiedKorePattern
simpleExistsUnifiedPatternWithType _ = simpleExistsUnifiedPattern

simpleExistsEqualsUnifiedPattern
    :: MetaOrObject level
    => VariableName
    -> OperandSort level
    -> ResultSort level
    -> VerifiedKorePattern
simpleExistsEqualsUnifiedPattern
    (VariableName name)
    (OperandSort operandSort)
    (ResultSort resultSort)
  =
    toKorePattern
        (mkExists
            var
            (mkEquals resultSort variablePattern' variablePattern')
        )
  where
    variablePattern' = mkVar var
    var =
        Variable
            { variableName = testId name
            , variableSort = operandSort
            }

applicationObjectUnifiedPatternWithChildren
    :: SymbolName -> [CommonKorePattern] -> CommonKorePattern
applicationObjectUnifiedPatternWithChildren name unifiedPatterns =
    asCommonKorePattern
        ( applicationPatternWithChildren name unifiedPatterns
        :: Pattern Meta Domain.Builtin Variable CommonKorePattern)

applicationPatternWithChildren
    :: SymbolName
    -> [child]
    -> Pattern level dom v child
applicationPatternWithChildren (SymbolName name) unifiedPatterns =
    ApplicationPattern Application
        { applicationSymbolOrAlias = SymbolOrAlias
            { symbolOrAliasConstructor = testId name
            , symbolOrAliasParams = []
            }
        , applicationChildren = unifiedPatterns
        }

applicationUnifiedPatternWithParams
    :: MetaOrObject level
    => Sort level
    -> SymbolName
    -> [Sort level]
    -> VerifiedKorePattern
applicationUnifiedPatternWithParams resultSort (SymbolName name) params =
    toKorePattern
        (mkApp
            resultSort
            SymbolOrAlias
                { symbolOrAliasConstructor = testId name
                , symbolOrAliasParams = params
                }
            []
        )
