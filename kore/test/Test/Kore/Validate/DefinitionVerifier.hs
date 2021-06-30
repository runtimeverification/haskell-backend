module Test.Kore.Validate.DefinitionVerifier (
    ErrorStack (..),
    SortName (..),
    NamePrefix (..),
    TestedPatternSort (..),
    SortVariablesThatMustBeDeclared (..),
    DeclaredSort (..),
    ExpectedErrorMessage (..),
    TestData (..),
    ResultSort (..),
    OperandSort (..),
    expectSuccess,
    simpleDefinitionFromSentences,
    simpleExistsPattern,
    simpleMuPattern,
    simpleNuPattern,
    applicationPatternWithChildren,
    simpleExistsParsedPattern,
    simpleExistsEqualsParsedPattern,
    applicationParsedPatternWithParams,
    variableParsedPattern,
    stringParsedPattern,
    simpleSort,
    variable,
    setVariable,
    simpleSortSentence,
    sortSentenceWithSortParameters,
    sortSentenceWithAttributes,
    simpleSymbolSentence,
    symbolSentenceWithParametersAndArguments,
    symbolSentenceWithSortParametersAux,
    sentenceSymbolWithAttributes,
    symbolSentenceWithParamsArgsAndAttrs,
    importSentence,
    SymbolName (..),
    objectSymbolSentenceWithArguments,
    symbolSentenceWithSortParameters,
    AliasName (..),
    simpleAliasSentence,
    aliasSentenceWithSortParameters,
    objectAliasSentenceWithArguments,
    metaAliasSentenceWithSortParameters,
    sentenceAliasWithResultSort,
    sentenceAliasWithSortArgument,
    sentenceAliasWithSortArgument',
    successTestData,
    successTestDataGroup,
    failureTestData,
    failureTestDataGroup,
    axiomSentenceWithParamsAndAttrs,
    axiomSentenceWithSortParameters,
    expectFailureWithError,
    objectVariableSort,
    simpleSortActual,
    SortVariableName (..),
    namedSortVariable,
) where

import Data.Text (
    Text,
 )
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin as Builtin
import Kore.Debug
import Kore.Error
import Kore.Internal.ApplicationSorts
import Kore.Internal.TermLike (
    TermLike,
 )
import qualified Kore.Internal.TermLike as Internal
import Kore.Sort
import Kore.Syntax hiding (
    PatternF (..),
 )
import Kore.Syntax.Definition
import qualified Kore.Syntax.PatternF as Syntax
import Kore.Unparser (
    unparseToString,
 )
import Kore.Validate.DefinitionVerifier
import Kore.Validate.Error
import Prelude.Kore
import Test.Kore
import Test.Kore.Builtin.External
import Test.Tasty (
    TestTree,
    testGroup,
 )
import Test.Tasty.HUnit (
    assertEqual,
    assertFailure,
    testCase,
 )

newtype ExpectedErrorMessage = ExpectedErrorMessage String
newtype ErrorStack = ErrorStack [String]
data TestData = TestData
    { testDataDescription :: !String
    , testDataError :: !(Error VerifyError)
    , testDataDefinition :: !(Definition ParsedSentence)
    }
failureTestDataGroup ::
    HasCallStack =>
    String ->
    ExpectedErrorMessage ->
    ErrorStack ->
    [TestData] ->
    TestTree
failureTestDataGroup description errorMessage errorStack testData =
    testGroup
        description
        (map (failureTestData errorMessage errorStack) testData)
failureTestData ::
    HasCallStack =>
    ExpectedErrorMessage ->
    ErrorStack ->
    TestData ->
    TestTree
failureTestData
    (ExpectedErrorMessage message)
    (ErrorStack stack)
    testData =
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
expectSuccess ::
    HasCallStack =>
    String ->
    Definition ParsedSentence ->
    TestTree
expectSuccess description unverifiedDefinition =
    testCase
        description
        ( assertEqual
            ( "Expecting verification success! Definition:\n"
                ++ printDefinition unverifiedDefinition
            )
            verifySuccess
            (verifyDefinition Builtin.koreVerifiers unverifiedDefinition)
        )
expectFailureWithError ::
    HasCallStack =>
    String ->
    Error VerifyError ->
    Definition ParsedSentence ->
    TestTree
expectFailureWithError description expectedError unverifiedDefinition =
    testCase
        description
        ( case verifyDefinition Builtin.koreVerifiers unverifiedDefinition of
            Right _ ->
                assertFailure
                    ( "Expecting verification failure! Definition:\n"
                        ++ printDefinition unverifiedDefinition
                    )
            Left actualError ->
                assertEqual
                    ( "Expecting a certain error! Definition:\n"
                        ++ printDefinition unverifiedDefinition
                    )
                    expectedError
                    actualError
        )
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
newtype NamePrefix = NamePrefix Text
newtype OperandSort = OperandSort Sort
newtype ResultSort = ResultSort Sort
newtype DeclaredSort = DeclaredSort Sort
newtype TestedPatternSort = TestedPatternSort Sort
newtype SortVariablesThatMustBeDeclared
    = SortVariablesThatMustBeDeclared [SortVariable]
simpleDefinitionFromSentences ::
    ModuleName ->
    [sentence] ->
    Definition sentence
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
    asSentence
        SentenceSort
            { sentenceSortName = testId name :: Id
            , sentenceSortParameters = []
            , sentenceSortAttributes = Attributes []
            }
simpleAliasSentence :: AliasName -> SortName -> ParsedSentence
simpleAliasSentence alias sort =
    asSentence @ParsedSentenceAlias (simpleAliasSentenceAux alias sort r)
  where
    r = externalize $ Internal.mkTop (simpleSort sort)
simpleAliasSentenceAux ::
    AliasName ->
    SortName ->
    patternType ->
    SentenceAlias patternType
simpleAliasSentenceAux (AliasName name) (SortName sort) r =
    SentenceAlias
        { sentenceAliasAlias =
            Alias
                { aliasConstructor = testId name
                , aliasParams = []
                }
        , sentenceAliasSorts = []
        , sentenceAliasResultSort =
            SortActualSort
                SortActual
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
simpleSymbolSentenceAux :: SymbolName -> SortName -> SentenceSymbol
simpleSymbolSentenceAux (SymbolName name) (SortName sort) =
    SentenceSymbol
        { sentenceSymbolSymbol =
            Symbol
                { symbolConstructor = testId name
                , symbolParams = []
                }
        , sentenceSymbolSorts = []
        , sentenceSymbolResultSort =
            SortActualSort
                SortActual
                    { sortActualName = testId sort
                    , sortActualSorts = []
                    }
        , sentenceSymbolAttributes = Attributes []
        }
importSentence :: ModuleName -> ParsedSentence
importSentence name =
    asSentence
        SentenceImport
            { sentenceImportModuleName = name
            , sentenceImportAttributes = Attributes []
            }

sortSentenceWithSortParameters ::
    SortName -> [SortVariable] -> ParsedSentence
sortSentenceWithSortParameters (SortName name) parameters =
    asSentence
        SentenceSort
            { sentenceSortName = testId name
            , sentenceSortParameters = parameters
            , sentenceSortAttributes = Attributes []
            }

sortSentenceWithAttributes ::
    SortName -> [SortVariable] -> [ParsedPattern] -> ParsedSentence
sortSentenceWithAttributes (SortName name) parameters attributes =
    asSentence
        SentenceSort
            { sentenceSortName = testId name
            , sentenceSortParameters = parameters
            , sentenceSortAttributes = Attributes attributes
            }

metaAliasSentenceWithSortParameters ::
    AliasName -> Sort -> [SortVariable] -> ParsedSentence
metaAliasSentenceWithSortParameters
    (AliasName name)
    sort
    parameters =
        asSentence @ParsedSentenceAlias
            SentenceAlias
                { sentenceAliasAlias =
                    Alias
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
                    externalize $ Internal.mkTop sort
                , sentenceAliasAttributes = Attributes []
                }

aliasSentenceWithSortParameters ::
    AliasName ->
    SortName ->
    [SortVariable] ->
    patternType ->
    SentenceAlias patternType
aliasSentenceWithSortParameters (AliasName name) (SortName sort) parameters r =
    SentenceAlias
        { sentenceAliasAlias =
            Alias
                { aliasConstructor = testId name
                , aliasParams = parameters
                }
        , sentenceAliasSorts = []
        , sentenceAliasResultSort =
            SortActualSort
                SortActual
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

sentenceAliasWithSortArgument ::
    AliasName ->
    Sort ->
    Sort ->
    [SortVariable] ->
    patternType ->
    SentenceAlias patternType
sentenceAliasWithSortArgument
    (AliasName name)
    sortArgument
    resultSort
    parameters
    r =
        SentenceAlias
            { sentenceAliasAlias =
                Alias
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
                        [inject $ mkElementVariable (testId "x") sortArgument]
                    }
            , sentenceAliasRightPattern = r
            , sentenceAliasAttributes = Attributes []
            }

sentenceAliasWithSortArgument' ::
    AliasName ->
    Sort ->
    Sort ->
    [SortVariable] ->
    patternType ->
    SentenceAlias patternType
sentenceAliasWithSortArgument'
    (AliasName name)
    sortArgument
    resultSort
    parameters
    r =
        SentenceAlias
            { sentenceAliasAlias =
                Alias
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
                        [inject $ mkSetVariable (testId "x") sortArgument]
                    }
            , sentenceAliasRightPattern = r
            , sentenceAliasAttributes = Attributes []
            }

sentenceSymbolWithAttributes ::
    SymbolName ->
    [SortVariable] ->
    Sort ->
    [ParsedPattern] ->
    ParsedSentenceSymbol
sentenceSymbolWithAttributes (SymbolName name) params sort attributes =
    SentenceSymbol
        { sentenceSymbolSymbol =
            Symbol
                { symbolConstructor = testId name
                , symbolParams = params
                }
        , sentenceSymbolSorts = []
        , sentenceSymbolResultSort = sort
        , sentenceSymbolAttributes = Attributes attributes
        }

symbolSentenceWithSortParameters ::
    SymbolName -> Sort -> [SortVariable] -> ParsedSentence
symbolSentenceWithSortParameters name sort params =
    asSentence $ symbolSentenceWithSortParametersAux name sort params

symbolSentenceWithSortParametersAux ::
    SymbolName ->
    Sort ->
    [SortVariable] ->
    SentenceSymbol
symbolSentenceWithSortParametersAux (SymbolName name) sort parameters =
    SentenceSymbol
        { sentenceSymbolSymbol =
            Symbol
                { symbolConstructor = testId name
                , symbolParams = parameters
                }
        , sentenceSymbolSorts = []
        , sentenceSymbolResultSort = sort
        , sentenceSymbolAttributes = Attributes []
        }

axiomSentenceWithParamsAndAttrs ::
    patternType ->
    [SortVariable] ->
    [AttributePattern] ->
    Sentence patternType
axiomSentenceWithParamsAndAttrs
    pattern'
    parameters
    attrs =
        SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = parameters
                , sentenceAxiomPattern = pattern'
                , sentenceAxiomAttributes = Attributes attrs
                }

axiomSentenceWithSortParameters ::
    patternType -> [SortVariable] -> Sentence patternType
axiomSentenceWithSortParameters pattern' parameters =
    axiomSentenceWithParamsAndAttrs pattern' parameters []

sentenceAliasWithResultSort ::
    AliasName ->
    Sort ->
    [SortVariable] ->
    patternType ->
    SentenceAlias patternType
sentenceAliasWithResultSort (AliasName name) sort parameters r =
    SentenceAlias
        { sentenceAliasAlias =
            Alias
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

objectSymbolSentenceWithArguments ::
    SymbolName -> Sort -> [Sort] -> ParsedSentence
objectSymbolSentenceWithArguments = symbolSentenceWithArguments

symbolSentenceWithArguments ::
    SymbolName -> Sort -> [Sort] -> ParsedSentence
symbolSentenceWithArguments name =
    symbolSentenceWithParametersAndArguments name []

symbolSentenceWithParametersAndArguments ::
    SymbolName ->
    [SortVariable] ->
    Sort ->
    [Sort] ->
    Sentence patternType
symbolSentenceWithParametersAndArguments
    (SymbolName name)
    params
    sort
    operandSorts =
        SentenceSymbolSentence
            SentenceSymbol
                { sentenceSymbolSymbol =
                    Symbol
                        { symbolConstructor = testId name
                        , symbolParams = params
                        }
                , sentenceSymbolSorts = operandSorts
                , sentenceSymbolResultSort = sort
                , sentenceSymbolAttributes =
                    Attributes [] :: Attributes
                }

symbolSentenceWithParamsArgsAndAttrs ::
    SymbolName ->
    [SortVariable] ->
    Sort ->
    [Sort] ->
    [ParsedPattern] ->
    Sentence patternType
symbolSentenceWithParamsArgsAndAttrs
    (SymbolName name)
    params
    sort
    operandSorts
    attrs =
        SentenceSymbolSentence
            SentenceSymbol
                { sentenceSymbolSymbol =
                    Symbol
                        { symbolConstructor = testId name
                        , symbolParams = params
                        }
                , sentenceSymbolSorts = operandSorts
                , sentenceSymbolResultSort = sort
                , sentenceSymbolAttributes =
                    Attributes attrs
                }

objectAliasSentenceWithArguments ::
    AliasName -> Sort -> [SomeVariable VariableName] -> ParsedSentence
objectAliasSentenceWithArguments a b c =
    aliasSentenceWithArguments
        a
        b
        c
        (externalize $ Internal.mkTop b)

aliasSentenceWithArguments ::
    AliasName ->
    Sort ->
    [SomeVariable VariableName] ->
    patternType ->
    Sentence patternType
aliasSentenceWithArguments (AliasName name) sort operands r =
    SentenceAliasSentence
        SentenceAlias
            { sentenceAliasAlias =
                Alias
                    { aliasConstructor = testId name
                    , aliasParams = []
                    }
            , sentenceAliasSorts = variableSort <$> operands
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
    externalize . Internal.mkStringLiteral

variable :: Text -> Sort -> ElementVariable VariableName
variable name sort = mkElementVariable (testId name) sort

setVariable :: Text -> Sort -> SetVariable VariableName
setVariable name sort = mkSetVariable (testId ("@" <> name)) sort

variableTermLike :: Text -> Sort -> TermLike VariableName
variableTermLike name sort = Internal.mkElemVar (variable name sort)

variableParsedPattern :: Text -> Sort -> ParsedPattern
variableParsedPattern name sort =
    externalize $ variableTermLike name sort

simpleExistsPattern ::
    ElementVariable VariableName ->
    Sort ->
    Syntax.PatternF VariableName ParsedPattern
simpleExistsPattern quantifiedVariable resultSort =
    Syntax.ExistsF
        Exists
            { existsSort = resultSort
            , existsVariable = quantifiedVariable
            , existsChild =
                externalize $ Internal.mkElemVar quantifiedVariable
            }

simpleMuPattern ::
    SetVariable VariableName ->
    Syntax.PatternF VariableName ParsedPattern
simpleMuPattern quantifiedVariable =
    Syntax.MuF
        Mu
            { muVariable = quantifiedVariable
            , muChild =
                externalize $ Internal.mkSetVar quantifiedVariable
            }

simpleNuPattern ::
    SetVariable VariableName ->
    Syntax.PatternF VariableName ParsedPattern
simpleNuPattern quantifiedVariable =
    Syntax.NuF
        Nu
            { nuVariable = quantifiedVariable
            , nuChild =
                externalize $ Internal.mkSetVar quantifiedVariable
            }

simpleExistsUnifiedPattern ::
    Text -> Sort -> TermLike VariableName
simpleExistsUnifiedPattern name sort =
    Internal.mkExists quantifiedVariable (Internal.mkElemVar quantifiedVariable)
  where
    quantifiedVariable = variable name sort

simpleExistsParsedPattern :: Text -> Sort -> ParsedPattern
simpleExistsParsedPattern name sort =
    externalize $ simpleExistsUnifiedPattern name sort

simpleExistsEqualsParsedPattern ::
    Text ->
    OperandSort ->
    ResultSort ->
    ParsedPattern
simpleExistsEqualsParsedPattern name operandSort resultSort =
    externalize $
        simpleExistsEqualsTermLike name operandSort resultSort

simpleExistsEqualsTermLike ::
    Text ->
    OperandSort ->
    ResultSort ->
    TermLike VariableName
simpleExistsEqualsTermLike
    name
    (OperandSort operandSort)
    (ResultSort resultSort) =
        Internal.mkExists var $
            Internal.mkEquals resultSort variablePattern' variablePattern'
      where
        variablePattern' = Internal.mkElemVar var
        var = mkElementVariable (testId name) operandSort

applicationPatternWithChildren ::
    SymbolName ->
    [child] ->
    Syntax.PatternF v child
applicationPatternWithChildren (SymbolName name) unifiedPatterns =
    Syntax.ApplicationF
        Application
            { applicationSymbolOrAlias =
                SymbolOrAlias
                    { symbolOrAliasConstructor = testId name
                    , symbolOrAliasParams = []
                    }
            , applicationChildren = unifiedPatterns
            }

applicationParsedPatternWithParams ::
    Sort ->
    SymbolName ->
    [Sort] ->
    ParsedPattern
applicationParsedPatternWithParams resultSort name params =
    externalize $
        applicationUnifiedPatternWithParams resultSort name params

applicationUnifiedPatternWithParams ::
    Sort ->
    SymbolName ->
    [Sort] ->
    TermLike VariableName
applicationUnifiedPatternWithParams resultSort (SymbolName name) params =
    Internal.mkApplySymbol
        Internal.Symbol
            { symbolConstructor = testId name
            , symbolParams = params
            , symbolAttributes = Attribute.defaultSymbolAttributes
            , symbolSorts = applicationSorts [] resultSort
            }
        []
