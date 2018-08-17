module Test.Kore.ASTVerifier.DefinitionVerifier where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
       ( HasCallStack, assertEqual, assertFailure, testCase )

import Data.Functor.Foldable
import Data.Proxy
       ( Proxy (..) )

import Kore.AST.Common
import Kore.AST.Kore
import Kore.AST.MetaOrObject
import Kore.AST.Sentence
import Kore.ASTPrettyPrint
import Kore.ASTVerifier.DefinitionVerifier
import Kore.ASTVerifier.Error
import qualified Kore.Builtin as Builtin
import Kore.Error
import Kore.Implicit.Attributes
import Kore.Implicit.ImplicitSorts
import Kore.Unparser.Unparse

import Test.Kore

newtype ExpectedErrorMessage = ExpectedErrorMessage String
newtype ErrorStack = ErrorStack [String]

data TestData = TestData
    { testDataDescription :: !String
    , testDataError       :: !(Error VerifyError)
    , testDataDefinition  :: !KoreDefinition
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

expectSuccess :: HasCallStack => String -> KoreDefinition -> TestTree
expectSuccess description definition =
    testCase
        description
        (assertEqual
            (  "Expecting verification success! Definition:\n"
            ++ printDefinition definition
            )
            verifySuccess
            (verifyDefinition
                attributesVerificationForTests
                Builtin.koreBuiltins
                definition
            )
        )

expectFailureWithError
    :: HasCallStack => String -> Error VerifyError -> KoreDefinition -> TestTree
expectFailureWithError description expectedError definition =
    testCase
        description
        (case
            verifyDefinition
                attributesVerificationForTests
                Builtin.koreBuiltins
                definition
          of
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

attributesVerificationForTests :: AttributesVerification ImplicitAttributes
attributesVerificationForTests = defaultAttributesVerification Proxy

printDefinition :: KoreDefinition -> String
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

simpleDefinitionFromSentences :: ModuleName -> [KoreSentence] -> KoreDefinition
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
simpleSortSentence :: SortName -> KoreSentence
simpleSortSentence (SortName name) =
    asSentence
        (SentenceSort
            { sentenceSortName = testId name
            , sentenceSortParameters = []
            , sentenceSortAttributes = Attributes []
            }::KoreSentenceSort Object
        )

simpleMetaAliasSentence :: AliasName -> SortName -> KoreSentence
simpleMetaAliasSentence alias sort =
    asSentence
        (simpleAliasSentence alias sort l r ::KoreSentenceAlias Meta)
  where
    l = TopPattern $ Top { topSort = patternMetaSort }
    r = TopPattern $ Top { topSort = patternMetaSort }

simpleObjectAliasSentence :: AliasName -> SortName -> KoreSentence
simpleObjectAliasSentence alias sort =
   asSentence (simpleAliasSentence alias sort l r ::KoreSentenceAlias Object)
   where
    l = TopPattern $ Top { topSort = simpleSort sort }
    r = TopPattern $ Top { topSort = simpleSort sort }

simpleAliasSentence
    :: AliasName
    -> SortName
    -> Pattern level Variable (Fix (UnifiedPattern Variable))
    -> Pattern level Variable (Fix (UnifiedPattern Variable))
    -> KoreSentenceAlias level
simpleAliasSentence (AliasName name) (SortName sort) l r =
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
        , sentenceAliasLeftPattern = l
        , sentenceAliasRightPattern = r
        , sentenceAliasAttributes = Attributes []
        }

simpleMetaSymbolSentence :: SymbolName -> SortName -> KoreSentence
simpleMetaSymbolSentence name sort =
    asSentence (simpleSymbolSentence name sort::KoreSentenceSymbol Meta)

simpleObjectSymbolSentence :: SymbolName -> SortName -> KoreSentence
simpleObjectSymbolSentence name sort =
    asSentence (simpleSymbolSentence name sort::KoreSentenceSymbol Object)

simpleSymbolSentence :: SymbolName -> SortName -> KoreSentenceSymbol level
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

simpleAxiomSentence :: CommonKorePattern -> KoreSentence
simpleAxiomSentence unifiedPattern =
    asSentence
        (SentenceAxiom
            { sentenceAxiomParameters = []
            , sentenceAxiomPattern = unifiedPattern
            , sentenceAxiomAttributes = Attributes []
            }::KoreSentenceAxiom
        )

importSentence :: ModuleName -> KoreSentence
importSentence name =
    asSentence
        (SentenceImport
            { sentenceImportModuleName = name
            , sentenceImportAttributes = Attributes []
            }::KoreSentenceImport
        )

sortSentenceWithSortParameters
    :: SortName -> [SortVariable Object] -> KoreSentence
sortSentenceWithSortParameters (SortName name) parameters =
    asSentence
        (SentenceSort
            { sentenceSortName = testId name
            , sentenceSortParameters = parameters
            , sentenceSortAttributes = Attributes []
            }::KoreSentenceSort Object
        )

aliasSentenceWithSort
    :: AliasName -> Sort Meta -> KoreSentence
aliasSentenceWithSort (AliasName name) sort =
    constructUnifiedSentence SentenceAliasSentence $
        SentenceAlias
            { sentenceAliasAlias = Alias
                { aliasConstructor = testId name
                , aliasParams = []
                }
            , sentenceAliasSorts = []
            , sentenceAliasResultSort = sort
            , sentenceAliasLeftPattern = TopPattern $ Top { topSort = patternMetaSort }
            , sentenceAliasRightPattern = TopPattern $ Top { topSort = patternMetaSort }
            , sentenceAliasAttributes =
                Attributes [] :: Attributes
            }

metaAliasSentenceWithSortParameters
    :: AliasName -> Sort Meta -> [SortVariable Meta] -> KoreSentence
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
            , sentenceAliasLeftPattern = TopPattern $ Top { topSort = patternMetaSort }
            , sentenceAliasRightPattern = TopPattern $ Top { topSort = patternMetaSort }
            , sentenceAliasAttributes = Attributes []
            }::KoreSentenceAlias Meta
        )


aliasSentenceWithSortParameters
    :: AliasName
    -> SortName
    -> [SortVariable level]
    -> Pattern level Variable (Fix (UnifiedPattern Variable))
    -> Pattern level Variable (Fix (UnifiedPattern Variable))
    -> KoreSentenceAlias level
aliasSentenceWithSortParameters
    (AliasName name) (SortName sort) parameters l r
  =
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
        , sentenceAliasLeftPattern = l
        , sentenceAliasRightPattern = r
        , sentenceAliasAttributes = Attributes []
        }

sentenceAliasWithSortArgument
    :: AliasName
    -> Sort level
    -> Sort level
    -> [SortVariable level]
    -> Pattern level Variable (Fix (UnifiedPattern Variable))
    -> Pattern level Variable (Fix (UnifiedPattern Variable))
    -> KoreSentenceAlias level
sentenceAliasWithSortArgument
    (AliasName name) sortArgument resultSort parameters l r
  =
    SentenceAlias
        { sentenceAliasAlias = Alias
            { aliasConstructor = testId name
            , aliasParams = parameters
            }
        , sentenceAliasSorts = [sortArgument]
        , sentenceAliasResultSort = resultSort
        , sentenceAliasLeftPattern = l
        , sentenceAliasRightPattern = r
        , sentenceAliasAttributes = Attributes []
        }

sentenceAliasWithAttributes
    :: AliasName
    -> [SortVariable level]
    -> Sort level
    -> [CommonKorePattern]
    -> Pattern level Variable (Fix (UnifiedPattern Variable))
    -> Pattern level Variable (Fix (UnifiedPattern Variable))
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
    :: SymbolName -> Sort Meta -> [SortVariable Meta] -> KoreSentence
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
            }::KoreSentenceSymbol Meta
        )

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
    :: CommonKorePattern -> [UnifiedSortVariable] -> KoreSentence
axiomSentenceWithSortParameters unifiedPattern parameters =
    asSentence
        (SentenceAxiom
            { sentenceAxiomParameters = parameters
            , sentenceAxiomPattern = unifiedPattern
            , sentenceAxiomAttributes = Attributes []
            }::KoreSentenceAxiom
        )

axiomSentenceWithAttributes
    :: [UnifiedSortVariable]
    -> CommonKorePattern
    -> [CommonKorePattern]
    -> KoreSentence
axiomSentenceWithAttributes parameters unifiedPattern attributes =
    asSentence
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
    -> Pattern level Variable (Fix (UnifiedPattern Variable))
    -> Pattern level Variable (Fix (UnifiedPattern Variable))
    -> KoreSentenceAlias level
sentenceAliasWithResultSort
    (AliasName name) sort parameters l r
  =
    SentenceAlias
        { sentenceAliasAlias = Alias
            { aliasConstructor = testId name
            , aliasParams = parameters
            }
        , sentenceAliasSorts = []
        , sentenceAliasResultSort = sort
        , sentenceAliasLeftPattern = l
        , sentenceAliasRightPattern = r
        , sentenceAliasAttributes = Attributes []
        }

symbolSentenceWithResultSort
    :: MetaOrObject level
    => SymbolName -> Sort level -> [SortVariable level] -> KoreSentence
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
    :: SymbolName -> Sort Object -> [Sort Object] -> KoreSentence
objectSymbolSentenceWithArguments = symbolSentenceWithArguments

symbolSentenceWithArguments
    :: MetaOrObject level
    => SymbolName -> Sort level -> [Sort level] -> KoreSentence
symbolSentenceWithArguments
    (SymbolName name) sort operandSorts
  = constructUnifiedSentence SentenceSymbolSentence $
        SentenceSymbol
            { sentenceSymbolSymbol = Symbol
                { symbolConstructor = testId name
                , symbolParams = []
                }
            , sentenceSymbolSorts = operandSorts
            , sentenceSymbolResultSort = sort
            , sentenceSymbolAttributes =
                Attributes [] :: Attributes
            }

objectAliasSentenceWithArguments
    :: AliasName -> Sort Object -> [Sort Object] -> KoreSentence
objectAliasSentenceWithArguments a b c =
    aliasSentenceWithArguments
        a
        b
        c
        (TopPattern $ Top { topSort = b })
        (TopPattern $ Top { topSort = b })

aliasSentenceWithArguments
    :: MetaOrObject level
    => AliasName
    -> Sort level
    -> [Sort level]
    -> Pattern level Variable (Fix (UnifiedPattern Variable))
    -> Pattern level Variable (Fix (UnifiedPattern Variable))
    -> KoreSentence
aliasSentenceWithArguments
    (AliasName name) sort operandSorts l r
  = constructUnifiedSentence SentenceAliasSentence $
        SentenceAlias
            { sentenceAliasAlias = Alias
                { aliasConstructor = testId name
                , aliasParams = []
                }
            , sentenceAliasSorts = operandSorts
            , sentenceAliasResultSort = sort
            , sentenceAliasLeftPattern = l
            , sentenceAliasRightPattern = r
            , sentenceAliasAttributes =
                Attributes [] :: Attributes
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

objectVariableSort :: SortVariableName -> Sort Object
objectVariableSort = sortVariableSort

sortVariableSort :: SortVariableName -> Sort level
sortVariableSort (SortVariableName sort) =
    SortVariableSort (SortVariable (testId sort))

sortVariable :: level -> SortVariableName -> SortVariable level
sortVariable _ (SortVariableName name) = SortVariable (testId name)

unifiedSortVariable
    :: MetaOrObject level => level -> SortVariableName -> UnifiedSortVariable
unifiedSortVariable x name =
    asUnified (sortVariable x name)

stringUnifiedPattern :: String -> CommonKorePattern
stringUnifiedPattern s =
    asKorePattern (StringLiteralPattern (StringLiteral s))

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

variablePattern :: VariableName -> Sort level -> Pattern level Variable p
variablePattern name sort =
    VariablePattern (variable name sort)

unifiedVariablePattern
    :: MetaOrObject level => VariableName -> Sort level -> CommonKorePattern
unifiedVariablePattern name sort =
    asKorePattern (variablePattern name sort)

simpleExistsPattern
    :: MetaOrObject level
    => Variable level -> Sort level -> Pattern level Variable CommonKorePattern
simpleExistsPattern quantifiedVariable resultSort =
    ExistsPattern Exists
        { existsSort = resultSort
        , existsVariable = quantifiedVariable
        , existsChild = asKorePattern (VariablePattern quantifiedVariable)
        }

simpleExistsUnifiedPattern
    :: MetaOrObject level => VariableName -> Sort level -> CommonKorePattern
simpleExistsUnifiedPattern name sort =
    asKorePattern
        ( simpleExistsPattern
            (variable name sort)
            sort
        )

simpleExistsObjectUnifiedPattern
    :: VariableName -> Sort Object -> CommonKorePattern
simpleExistsObjectUnifiedPattern = simpleExistsUnifiedPattern

simpleExistsUnifiedPatternWithType
    :: MetaOrObject level
    => level -> VariableName -> Sort level -> CommonKorePattern
simpleExistsUnifiedPatternWithType _ = simpleExistsUnifiedPattern

simpleExistsEqualsUnifiedPattern
    :: MetaOrObject level
    => VariableName
    -> OperandSort level
    -> ResultSort level
    -> CommonKorePattern
simpleExistsEqualsUnifiedPattern
    name
    (OperandSort operandSort)
    (ResultSort resultSort)
  =
    asKorePattern
        (ExistsPattern Exists
            { existsSort = resultSort
            , existsVariable = variable name operandSort
            , existsChild = asKorePattern
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
    :: SymbolName -> [CommonKorePattern] -> CommonKorePattern
applicationObjectUnifiedPatternWithChildren name unifiedPatterns =
    asKorePattern
        ( applicationPatternWithChildren name unifiedPatterns
        :: Pattern Meta Variable CommonKorePattern)

applicationPatternWithChildren
    :: SymbolName -> [CommonKorePattern] -> Pattern level v CommonKorePattern
applicationPatternWithChildren (SymbolName name) unifiedPatterns =
    ApplicationPattern Application
        { applicationSymbolOrAlias = SymbolOrAlias
            { symbolOrAliasConstructor = testId name
            , symbolOrAliasParams = []
            }
        , applicationChildren = unifiedPatterns
        }

applicationUnifiedPatternWithParams
    :: MetaOrObject level => SymbolName -> [Sort level] -> CommonKorePattern
applicationUnifiedPatternWithParams (SymbolName name) params =
    asKorePattern
        (ApplicationPattern Application
            { applicationSymbolOrAlias = SymbolOrAlias
                { symbolOrAliasConstructor = testId name
                , symbolOrAliasParams = params
                }
            , applicationChildren = []
            }
        )
