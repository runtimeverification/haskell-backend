module Test.Kore.ASTVerifier.DefinitionVerifier where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
       ( HasCallStack, assertEqual, assertFailure, testCase )

import qualified Data.Set as Set
import           Data.Text
                 ( Text )

import           Kore.AST.Pure
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
import           Kore.Step.Pattern hiding
                 ( freeVariables )
import           Kore.Unparser
                 ( unparseToString )
import qualified Kore.Verified.Pattern as Verified
import qualified Kore.Verified.Sentence as Verified

import Test.Kore

newtype ExpectedErrorMessage = ExpectedErrorMessage String
newtype ErrorStack = ErrorStack [String]

data TestData = TestData
    { testDataDescription :: !String
    , testDataError       :: !(Error VerifyError)
    , testDataDefinition  :: !(Definition Verified.Sentence)
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
    -> Definition Verified.Sentence
    -> TestTree
expectSuccess description (fmap eraseSentenceAnnotations -> definition) =
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
    -> Definition Verified.Sentence
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
    definition' = eraseSentenceAnnotations <$> definition

attributesVerificationForTests
    :: AttributesVerification Attribute.Null Attribute.Null
attributesVerificationForTests = defaultNullAttributesVerification

printDefinition :: ParsedDefinition -> String
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
    -> [Verified.Sentence]
    -> Definition Verified.Sentence
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
simpleSortSentence :: SortName -> Verified.Sentence
simpleSortSentence (SortName name) =
    asSentence
        (SentenceSort
            { sentenceSortName = testId name :: Id Object
            , sentenceSortParameters = []
            , sentenceSortAttributes = Attributes []
            }
            :: Verified.SentenceSort
        )

simpleMetaAliasSentence :: AliasName -> SortName -> Verified.Sentence
simpleMetaAliasSentence alias sort =
    asSentence (simpleAliasSentence alias sort r)
  where
    r = mkTop (simpleSort sort :: Sort Meta)

simpleObjectAliasSentence :: AliasName -> SortName -> Verified.Sentence
simpleObjectAliasSentence alias sort =
   asSentence (simpleAliasSentence alias sort r)
  where
    r = mkTop (simpleSort sort :: Sort Object)

simpleAliasSentence
    :: AliasName
    -> SortName
    -> Verified.Pattern
    -> Verified.SentenceAlias
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

simpleMetaSymbolSentence :: SymbolName -> SortName -> Verified.Sentence
simpleMetaSymbolSentence name sort =
    asSentence (simpleSymbolSentence name sort)

simpleObjectSymbolSentence :: SymbolName -> SortName -> Verified.Sentence
simpleObjectSymbolSentence name sort =
    asSentence (simpleSymbolSentence name sort)

simpleSymbolSentence
    :: SymbolName
    -> SortName
    -> Verified.SentenceSymbol
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

simpleAxiomSentence :: Verified.Pattern -> Verified.Sentence
simpleAxiomSentence unifiedPattern =
    SentenceAxiomSentence
        (SentenceAxiom
            { sentenceAxiomParameters = []
            , sentenceAxiomPattern = unifiedPattern
            , sentenceAxiomAttributes = Attributes []
            }
            :: Verified.SentenceAxiom
        )

importSentence :: ModuleName -> Verified.Sentence
importSentence name =
    asSentence
        (SentenceImport
            { sentenceImportModuleName = name
            , sentenceImportAttributes = Attributes []
            }
            :: Verified.SentenceImport
        )

sortSentenceWithSortParameters
    :: SortName -> [SortVariable Object] -> Verified.Sentence
sortSentenceWithSortParameters (SortName name) parameters =
    asSentence
        (SentenceSort
            { sentenceSortName = testId name
            , sentenceSortParameters = parameters
            , sentenceSortAttributes = Attributes []
            }
            :: Verified.SentenceSort
        )

aliasSentenceWithSort
    :: AliasName -> Sort Meta -> Verified.Sentence
aliasSentenceWithSort (AliasName name) sort =
    SentenceAliasSentence
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
            , sentenceAliasRightPattern = mkTop patternMetaSort
            , sentenceAliasAttributes =
                Attributes [] :: Attributes
            }

metaAliasSentenceWithSortParameters
    :: AliasName -> Sort Meta -> [SortVariable Meta] -> Verified.Sentence
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
            , sentenceAliasRightPattern = mkTop sort
            , sentenceAliasAttributes = Attributes []
            }
            :: Verified.SentenceAlias
        )


aliasSentenceWithSortParameters
    :: AliasName
    -> SortName
    -> [SortVariable Object]
    -> Verified.Pattern
    -> Verified.SentenceAlias
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
    :: AliasName
    -> Sort Object
    -> Sort Object
    -> [SortVariable Object]
    -> Verified.Pattern
    -> Verified.SentenceAlias
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
                        , variableCounter = mempty
                        , variableSort = sortArgument
                        }
                    ]
                }
        , sentenceAliasRightPattern = r
        , sentenceAliasAttributes = Attributes []
        }

sentenceAliasWithAttributes
    :: AliasName
    -> [SortVariable Object]
    -> Sort Object
    -> [ParsedPattern]
    -> Application Object (Variable Object)
    -> ParsedPattern
    -> ParsedSentenceAlias
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
    -> [SortVariable Object]
    -> Sort Object
    -> [ParsedPattern]
    -> ParsedSentenceSymbol
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
    :: SymbolName -> Sort Meta -> [SortVariable Meta] -> Verified.Sentence
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
            :: Verified.SentenceSymbol
        )

symbolSentenceWithSortParameters
    :: SymbolName
    -> SortName
    -> [SortVariable Object]
    -> Verified.SentenceSymbol
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
    :: Verified.Pattern -> [SortVariable Object] -> Verified.Sentence
axiomSentenceWithSortParameters unifiedPattern parameters =
    SentenceAxiomSentence
        (SentenceAxiom
            { sentenceAxiomParameters = parameters
            , sentenceAxiomPattern = unifiedPattern
            , sentenceAxiomAttributes = Attributes []
            }
            :: Verified.SentenceAxiom
        )

axiomSentenceWithAttributes
    :: [SortVariable Object]
    -> ParsedPattern
    -> [ParsedPattern]
    -> ParsedSentence
axiomSentenceWithAttributes parameters unifiedPattern attributes =
    SentenceAxiomSentence
        (SentenceAxiom
            { sentenceAxiomParameters = parameters
            , sentenceAxiomPattern = unifiedPattern
            , sentenceAxiomAttributes = Attributes attributes
            }::ParsedSentenceAxiom
        )

sentenceAliasWithResultSort
    :: AliasName
    -> Sort Object
    -> [SortVariable Object]
    -> Verified.Pattern
    -> Verified.SentenceAlias
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
    :: SymbolName -> Sort Object -> [SortVariable Object] -> Verified.Sentence
symbolSentenceWithResultSort
    (SymbolName name) sort parameters
  = SentenceSymbolSentence
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
    :: SymbolName -> Sort Object -> [Sort Object] -> Verified.Sentence
objectSymbolSentenceWithArguments = symbolSentenceWithArguments

symbolSentenceWithArguments
    :: SymbolName -> Sort Object -> [Sort Object] -> Verified.Sentence
symbolSentenceWithArguments name
  = symbolSentenceWithParametersAndArguments name []

objectSymbolSentenceWithParametersAndArguments
    :: SymbolName
    -> [SortVariable Object]
    -> Sort Object
    -> [Sort Object]
    -> Verified.Sentence
objectSymbolSentenceWithParametersAndArguments
  = symbolSentenceWithParametersAndArguments

symbolSentenceWithParametersAndArguments
    :: SymbolName
    -> [SortVariable Object]
    -> Sort Object
    -> [Sort Object]
    -> Verified.Sentence
symbolSentenceWithParametersAndArguments
    (SymbolName name) params sort operandSorts
  = SentenceSymbolSentence
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
    :: AliasName -> Sort Object -> [Variable Object] -> Verified.Sentence
objectAliasSentenceWithArguments a b c =
    aliasSentenceWithArguments
        a
        b
        c
        (asPurePattern $ valid :< top')
  where
    top' = TopPattern Top { topSort = b }
    valid = Valid { patternSort = b, freeVariables = Set.empty }

aliasSentenceWithArguments
    :: AliasName
    -> Sort Object
    -> [Variable Object]
    -> Verified.Pattern
    -> Verified.Sentence
aliasSentenceWithArguments (AliasName name) sort operands r =
    SentenceAliasSentence
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
    => level -> SortVariableName -> (SortVariable level)
unifiedSortVariable _x (SortVariableName name) =
    (sortVariable name :: SortVariable level)

stringUnifiedPattern :: Text -> StepPattern Meta Variable
stringUnifiedPattern s = (mkStringLiteral s)

variable :: VariableName -> Sort level -> Variable level
variable (VariableName name) sort =
    Variable
        { variableName = testId name
        , variableCounter = mempty
        , variableSort = sort
        }

unifiedVariable
    :: MetaOrObject level
    => VariableName -> Sort level -> Variable level
unifiedVariable name sort =
    variable name sort

variablePattern :: VariableName -> Sort level -> Pattern level domain Variable p
variablePattern name sort =
    VariablePattern (variable name sort)

unifiedVariablePattern
    :: MetaOrObject level => VariableName -> Sort level -> StepPattern level Variable
unifiedVariablePattern name patternSort =
    asPurePattern (valid :< variablePattern name patternSort)
  where
    freeVariables = Set.singleton (variable name patternSort)
    valid = Valid { patternSort, freeVariables }

simpleExistsPattern
    :: MetaOrObject level
    => Variable level
    -> Sort level
    -> Pattern level domain Variable (StepPattern level Variable)
simpleExistsPattern quantifiedVariable resultSort =
    ExistsPattern Exists
        { existsSort = resultSort
        , existsVariable = quantifiedVariable
        , existsChild = mkVar quantifiedVariable
        }

simpleExistsUnifiedPattern
    :: MetaOrObject level => VariableName -> Sort level -> StepPattern level Variable
simpleExistsUnifiedPattern name sort =
    asPurePattern $ valid :< simpleExistsPattern (variable name sort) sort
  where
    valid = Valid { patternSort = sort, freeVariables = Set.empty }

simpleExistsObjectUnifiedPattern
    :: VariableName -> Sort Object -> StepPattern Object Variable
simpleExistsObjectUnifiedPattern = simpleExistsUnifiedPattern

simpleExistsUnifiedPatternWithType
    :: MetaOrObject level
    => level -> VariableName -> Sort level -> StepPattern level Variable
simpleExistsUnifiedPatternWithType _ = simpleExistsUnifiedPattern

simpleExistsEqualsUnifiedPattern
    :: MetaOrObject level
    => VariableName
    -> OperandSort level
    -> ResultSort level
    -> StepPattern level Variable
simpleExistsEqualsUnifiedPattern
    (VariableName name)
    (OperandSort operandSort)
    (ResultSort resultSort)
  =
    mkExists var
    $ mkEquals resultSort variablePattern' variablePattern'
  where
    variablePattern' = mkVar var
    var =
        Variable
            { variableName = testId name
            , variableCounter = mempty
            , variableSort = operandSort
            }

applicationObjectUnifiedPatternWithChildren
    :: SymbolName -> [ParsedPattern] -> ParsedPattern
applicationObjectUnifiedPatternWithChildren name unifiedPatterns =
    asParsedPattern
        ( applicationPatternWithChildren name unifiedPatterns
        :: Pattern Meta Domain.Builtin Variable ParsedPattern)

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
    -> StepPattern level Variable
applicationUnifiedPatternWithParams resultSort (SymbolName name) params =
    mkApp
        resultSort
        SymbolOrAlias
            { symbolOrAliasConstructor = testId name
            , symbolOrAliasParams = params
            }
        []
