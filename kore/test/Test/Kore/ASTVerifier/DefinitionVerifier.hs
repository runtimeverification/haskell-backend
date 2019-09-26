module Test.Kore.ASTVerifier.DefinitionVerifier where

import Test.Tasty
    ( TestTree
    , testGroup
    )
import Test.Tasty.HUnit
    ( HasCallStack
    , assertEqual
    , assertFailure
    , testCase
    )

import Data.Proxy
import Data.Text
    ( Text
    )

import Kore.ASTVerifier.DefinitionVerifier
import Kore.ASTVerifier.Error
import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin as Builtin
import Kore.Debug
import Kore.Error
import Kore.Internal.ApplicationSorts
import Kore.Internal.TermLike
    ( TermLike
    )
import qualified Kore.Internal.TermLike as Internal
import Kore.Sort
import Kore.Syntax hiding
    ( PatternF (..)
    )
import Kore.Syntax.Definition
import qualified Kore.Syntax.PatternF as Syntax
import Kore.Unparser
    ( unparseToString
    )
import Kore.Variables.UnifiedVariable
import qualified Kore.Verified as Verified

import Test.Kore

newtype ExpectedErrorMessage = ExpectedErrorMessage String
newtype ErrorStack = ErrorStack [String]

data TestData = TestData
    { testDataDescription :: !String
    , testDataError       :: !(Error VerifyError)
    , testDataDefinition  :: !(Definition ParsedSentence)
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
    -> Definition ParsedSentence
    -> TestTree
expectSuccess description unverifiedDefinition =
    testCase
        description
        (assertEqual
            (  "Expecting verification success! Definition:\n"
            ++ printDefinition unverifiedDefinition
            )
            verifySuccess
            (verifyDefinition
                attributesVerificationForTests
                Builtin.koreVerifiers
                unverifiedDefinition
            )
        )

expectFailureWithError
    :: HasCallStack
    => String
    -> Error VerifyError
    -> Definition ParsedSentence
    -> TestTree
expectFailureWithError description expectedError unverifiedDefinition =
    testCase
        description
        (case
            verifyDefinition
                attributesVerificationForTests
                Builtin.koreVerifiers
                unverifiedDefinition
          of
            Right _ ->
                assertFailure
                    (  "Expecting verification failure! Definition:\n"
                    ++ printDefinition unverifiedDefinition
                    )
            Left actualError ->
                assertEqual
                    ( "Expecting a certain error! Definition:\n"
                    ++ printDefinition unverifiedDefinition
                    )
                    expectedError actualError
        )

attributesVerificationForTests
    :: AttributesVerification Attribute.Symbol Attribute.Axiom
attributesVerificationForTests = defaultAttributesVerification Proxy Proxy

printDefinition :: ParsedDefinition -> String
printDefinition definition =
    (show . debug) definition
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
newtype OperandSort = OperandSort Sort
newtype ResultSort = ResultSort Sort
newtype DeclaredSort = DeclaredSort Sort
newtype TestedPatternSort = TestedPatternSort Sort
newtype SortVariablesThatMustBeDeclared =
    SortVariablesThatMustBeDeclared [SortVariable]

simpleDefinitionFromSentences
    :: ModuleName
    -> [sentence]
    -> Definition sentence
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

simpleSortSentence :: SortName -> ParsedSentence
simpleSortSentence (SortName name) =
    asSentence SentenceSort
        { sentenceSortName = testId name :: Id
        , sentenceSortParameters = []
        , sentenceSortAttributes = Attributes []
        }

simpleAliasSentence :: AliasName -> SortName -> ParsedSentence
simpleAliasSentence alias sort =
    asSentence (simpleAliasSentenceAux alias sort r)
  where
    r = Builtin.externalize $ Internal.mkTop (simpleSort sort)

simpleAliasSentenceAux
    :: AliasName
    -> SortName
    -> patternType
    -> SentenceAlias patternType
simpleAliasSentenceAux (AliasName name) (SortName sort) r =
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

simpleSymbolSentence :: SymbolName -> SortName -> ParsedSentence
simpleSymbolSentence name sort =
    asSentence (simpleSymbolSentenceAux name sort)

simpleSymbolSentenceAux
    :: SymbolName
    -> SortName
    -> SentenceSymbol patternType
simpleSymbolSentenceAux (SymbolName name) (SortName sort) =
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

importSentence :: ModuleName -> ParsedSentence
importSentence name =
    asSentence SentenceImport
        { sentenceImportModuleName = name
        , sentenceImportAttributes = Attributes []
        }

sortSentenceWithSortParameters
    :: SortName -> [SortVariable] -> ParsedSentence
sortSentenceWithSortParameters (SortName name) parameters =
    asSentence SentenceSort
        { sentenceSortName = testId name
        , sentenceSortParameters = parameters
        , sentenceSortAttributes = Attributes []
        }

sortSentenceWithAttributes
    :: SortName -> [SortVariable] -> [ParsedPattern] -> ParsedSentence
sortSentenceWithAttributes (SortName name) parameters attributes =
    asSentence SentenceSort
        { sentenceSortName = testId name
        , sentenceSortParameters = parameters
        , sentenceSortAttributes = Attributes attributes
        }

aliasSentenceWithSort
    :: AliasName -> Sort -> Verified.Sentence
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
            , sentenceAliasRightPattern = Internal.mkTop sort
            , sentenceAliasAttributes = Attributes []
            }

metaAliasSentenceWithSortParameters
    :: AliasName -> Sort -> [SortVariable] -> ParsedSentence
metaAliasSentenceWithSortParameters
    (AliasName name) sort parameters
  =
    asSentence SentenceAlias
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
            Builtin.externalize $ Internal.mkTop sort
        , sentenceAliasAttributes = Attributes []
        }

aliasSentenceWithSortParameters
    :: AliasName
    -> SortName
    -> [SortVariable]
    -> patternType
    -> SentenceAlias patternType
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
    -> Sort
    -> Sort
    -> [SortVariable]
    -> patternType
    -> SentenceAlias patternType
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
                    [ ElemVar $ ElementVariable Variable
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
    -> [SortVariable]
    -> Sort
    -> [ParsedPattern]
    -> Application SymbolOrAlias (UnifiedVariable Variable)
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
    -> [SortVariable]
    -> Sort
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

symbolSentenceWithSortParameters
    :: SymbolName -> Sort -> [SortVariable] -> ParsedSentence
symbolSentenceWithSortParameters name sort params =
    asSentence $ symbolSentenceWithSortParametersAux name sort params

symbolSentenceWithSortParametersAux
    :: SymbolName
    -> Sort
    -> [SortVariable]
    -> SentenceSymbol patternType
symbolSentenceWithSortParametersAux (SymbolName name) sort parameters =
    SentenceSymbol
        { sentenceSymbolSymbol = Symbol
            { symbolConstructor = testId name
            , symbolParams = parameters
            }
        , sentenceSymbolSorts = []
        , sentenceSymbolResultSort = sort
        , sentenceSymbolAttributes = Attributes []
        }

axiomSentenceWithSortParameters
    :: patternType -> [SortVariable] -> Sentence patternType
axiomSentenceWithSortParameters pattern' parameters =
    SentenceAxiomSentence SentenceAxiom
        { sentenceAxiomParameters = parameters
        , sentenceAxiomPattern = pattern'
        , sentenceAxiomAttributes = Attributes []
        }

axiomSentenceWithAttributes
    :: [SortVariable]
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
    -> Sort
    -> [SortVariable]
    -> patternType
    -> SentenceAlias patternType
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
    :: SymbolName -> Sort -> [SortVariable] -> ParsedSentence
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
    :: SymbolName -> Sort -> [Sort] -> ParsedSentence
objectSymbolSentenceWithArguments = symbolSentenceWithArguments

symbolSentenceWithArguments
    :: SymbolName -> Sort -> [Sort] -> ParsedSentence
symbolSentenceWithArguments name
  = symbolSentenceWithParametersAndArguments name []

objectSymbolSentenceWithParametersAndArguments
    :: SymbolName
    -> [SortVariable]
    -> Sort
    -> [Sort]
    -> Verified.Sentence
objectSymbolSentenceWithParametersAndArguments
  = symbolSentenceWithParametersAndArguments

symbolSentenceWithParametersAndArguments
    :: SymbolName
    -> [SortVariable]
    -> Sort
    -> [Sort]
    -> Sentence patternType
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
    :: AliasName -> Sort -> [UnifiedVariable Variable] -> ParsedSentence
objectAliasSentenceWithArguments a b c =
    aliasSentenceWithArguments
        a
        b
        c
        (Builtin.externalize $ Internal.mkTop b)

aliasSentenceWithArguments
    :: AliasName
    -> Sort
    -> [UnifiedVariable Variable]
    -> patternType
    -> Sentence patternType
aliasSentenceWithArguments (AliasName name) sort operands r =
    SentenceAliasSentence
        SentenceAlias
            { sentenceAliasAlias = Alias
                { aliasConstructor = testId name
                , aliasParams = []
                }
            , sentenceAliasSorts =
                foldMapVariable variableSort <$> operands
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

simpleSortActual :: SortName -> SortActual
simpleSortActual (SortName sort) =
    SortActual
        { sortActualName = testId sort
        , sortActualSorts = []
        }

simpleSort :: SortName -> Sort
simpleSort sortName =
    SortActualSort (simpleSortActual sortName)

objectVariableSort :: Text -> Sort
objectVariableSort name = sortVariableSort name

namedSortVariable :: SortVariableName -> SortVariable
namedSortVariable (SortVariableName name) = sortVariable name

stringParsedPattern :: Text -> ParsedPattern
stringParsedPattern =
    Builtin.externalize . Internal.mkStringLiteral

variable :: VariableName -> Sort -> ElementVariable Variable
variable (VariableName name) sort =
    ElementVariable Variable
        { variableName = testId name
        , variableCounter = mempty
        , variableSort = sort
        }

setVariable :: VariableName -> Sort -> SetVariable Variable
setVariable (VariableName name) sort =
    SetVariable Variable
        { variableName = testId ("@" <> name)
        , variableCounter = mempty
        , variableSort = sort
        }

variablePattern :: VariableName -> Sort -> Syntax.PatternF Variable p
variablePattern name sort =
    Syntax.VariableF $ Const $ ElemVar $ variable name sort

variableTermLike :: VariableName -> Sort -> TermLike Variable
variableTermLike name sort = Internal.mkElemVar (variable name sort)

variableParsedPattern :: VariableName -> Sort -> ParsedPattern
variableParsedPattern name sort =
    Builtin.externalize $ variableTermLike name sort

simpleExistsPattern
    :: ElementVariable Variable
    -> Sort
    -> Syntax.PatternF Variable ParsedPattern
simpleExistsPattern quantifiedVariable resultSort =
    Syntax.ExistsF Exists
        { existsSort = resultSort
        , existsVariable = quantifiedVariable
        , existsChild =
            Builtin.externalize $ Internal.mkElemVar quantifiedVariable
        }

simpleMuPattern
    :: SetVariable Variable
    -> Syntax.PatternF Variable ParsedPattern
simpleMuPattern quantifiedVariable =
    Syntax.MuF Mu
        { muVariable = quantifiedVariable
        , muChild =
            Builtin.externalize $ Internal.mkSetVar quantifiedVariable
        }

simpleNuPattern
    :: SetVariable Variable
    -> Syntax.PatternF Variable ParsedPattern
simpleNuPattern quantifiedVariable =
    Syntax.NuF Nu
        { nuVariable = quantifiedVariable
        , nuChild =
            Builtin.externalize $ Internal.mkSetVar quantifiedVariable
        }

simpleExistsUnifiedPattern
    :: VariableName -> Sort -> TermLike Variable
simpleExistsUnifiedPattern name sort =
    Internal.mkExists quantifiedVariable (Internal.mkElemVar quantifiedVariable)
  where
    quantifiedVariable = variable name sort

simpleExistsParsedPattern :: VariableName -> Sort -> ParsedPattern
simpleExistsParsedPattern name sort =
    Builtin.externalize $ simpleExistsUnifiedPattern name sort

simpleExistsUnifiedPatternWithType
    :: VariableName -> Sort -> TermLike Variable
simpleExistsUnifiedPatternWithType = simpleExistsUnifiedPattern

simpleExistsEqualsParsedPattern
    :: VariableName
    -> OperandSort
    -> ResultSort
    -> ParsedPattern
simpleExistsEqualsParsedPattern name operandSort resultSort =
    Builtin.externalize
    $ simpleExistsEqualsTermLike name operandSort resultSort

simpleExistsEqualsTermLike
    :: VariableName
    -> OperandSort
    -> ResultSort
    -> TermLike Variable
simpleExistsEqualsTermLike
    (VariableName name)
    (OperandSort operandSort)
    (ResultSort resultSort)
  =
    Internal.mkExists var
    $ Internal.mkEquals resultSort variablePattern' variablePattern'
  where
    variablePattern' = Internal.mkElemVar var
    var =
        ElementVariable Variable
            { variableName = testId name
            , variableCounter = mempty
            , variableSort = operandSort
            }

applicationObjectUnifiedPatternWithChildren
    :: SymbolName -> [ParsedPattern] -> ParsedPattern
applicationObjectUnifiedPatternWithChildren name unifiedPatterns =
    asParsedPattern
        (applicationPatternWithChildren name unifiedPatterns)

applicationPatternWithChildren
    :: SymbolName
    -> [child]
    -> Syntax.PatternF v child
applicationPatternWithChildren (SymbolName name) unifiedPatterns =
    Syntax.ApplicationF Application
        { applicationSymbolOrAlias = SymbolOrAlias
            { symbolOrAliasConstructor = testId name
            , symbolOrAliasParams = []
            }
        , applicationChildren = unifiedPatterns
        }

applicationParsedPatternWithParams
    :: Sort
    -> SymbolName
    -> [Sort]
    -> ParsedPattern
applicationParsedPatternWithParams resultSort name params =
    Builtin.externalize
    $ applicationUnifiedPatternWithParams resultSort name params

applicationUnifiedPatternWithParams
    :: Sort
    -> SymbolName
    -> [Sort]
    -> TermLike Variable
applicationUnifiedPatternWithParams resultSort (SymbolName name) params =
    Internal.mkApplySymbol
        Internal.Symbol
            { symbolConstructor = testId name
            , symbolParams = params
            , symbolAttributes = Attribute.defaultSymbolAttributes
            , symbolSorts = applicationSorts [] resultSort
            }
        []
