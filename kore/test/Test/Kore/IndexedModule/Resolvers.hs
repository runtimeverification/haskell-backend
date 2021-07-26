module Test.Kore.IndexedModule.Resolvers (
    test_resolvers,
    test_resolver_undefined_messages,
) where

import Data.Default
import qualified Data.List as List
import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import qualified Data.Ord
import Kore.Attribute.Function (
    Function (..),
 )
import qualified Kore.Attribute.Sort as Attribute
import Kore.Attribute.Symbol (
    Symbol (..),
 )
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin as Builtin
import Kore.Error
import Kore.IndexedModule.Error as Error
import Kore.IndexedModule.IndexedModule
import Kore.IndexedModule.Resolvers
import Kore.Internal.ApplicationSorts
import qualified Kore.Internal.TermLike as TermLike
import Kore.Sort
import Kore.Syntax
import Kore.Syntax.Definition
import Kore.Syntax.PatternF (
    groundHead,
 )
import Kore.Validate.DefinitionVerifier
import Prelude.Kore
import Test.Kore
import Test.Kore.Builtin.External
import Test.Kore.Validate.DefinitionVerifier
import Test.Tasty
import Test.Tasty.HUnit

objectS1 :: Sort
objectS1 = simpleSort (SortName "s1")

objectA :: SentenceSymbol
objectA =
    (TermLike.mkSymbol_ (testId "a") [] objectS1)
        { sentenceSymbolAttributes =
            Attributes [Attribute.functionAttribute]
        }

-- Two variations on a constructor axiom for 'objectA'.
axiomA, axiomA' :: SentenceAxiom ParsedPattern
axiomA =
    fmap externalize $
        TermLike.mkAxiom_ $ TermLike.applySymbol_ objectA []
axiomA' =
    fmap externalize $
        TermLike.mkAxiom [sortVariableR] $
            TermLike.mkForall x $
                TermLike.mkEquals sortR (TermLike.applySymbol_ objectA []) $
                    TermLike.mkElemVar x
  where
    x = TermLike.mkElementVariable "x" objectS1
    sortVariableR = SortVariable (testId "R")
    sortR = SortVariableSort sortVariableR

objectB :: SentenceAlias ParsedPattern
objectB =
    fmap externalize $
        TermLike.mkAlias_ (testId "b") objectS1 [] $ TermLike.mkTop objectS1

metaA :: SentenceSymbol
metaA = TermLike.mkSymbol_ (testId "#a") [] stringMetaSort

metaB :: SentenceAlias ParsedPattern
metaB =
    fmap externalize $
        TermLike.mkAlias_ (testId "#b") stringMetaSort [] $
            TermLike.mkTop stringMetaSort

testObjectModuleName :: ModuleName
testObjectModuleName = ModuleName "TEST-OBJECT-MODULE"

testMetaModuleName :: ModuleName
testMetaModuleName = ModuleName "TEST-META-MODULE"

testSubMainModuleName :: ModuleName
testSubMainModuleName = ModuleName "TEST-SUB-MAIN-MODULE"

testMainModuleName :: ModuleName
testMainModuleName = ModuleName "TEST-MAIN-MODULE"

strictAttribute :: ParsedPattern
strictAttribute = attributePattern_ (groundHead "strict" AstLocationTest)

testObjectModule :: Module ParsedSentence
testObjectModule =
    Module
        { moduleName = testObjectModuleName
        , moduleSentences =
            [ SentenceSortSentence
                SentenceSort
                    { sentenceSortName = testId "s1"
                    , sentenceSortParameters = []
                    , sentenceSortAttributes = Attributes [strictAttribute]
                    }
            , asSentence objectA
            , asSentence objectB
            , asSentence axiomA
            , asSentence axiomA'
            ]
        , moduleAttributes = Attributes [strictAttribute]
        }

testMetaModule :: Module ParsedSentence
testMetaModule =
    Module
        { moduleName = testMetaModuleName
        , moduleSentences =
            [ asSentence metaA
            , asSentence metaB
            ]
        , moduleAttributes = Attributes []
        }

subMainModule :: Module ParsedSentence
subMainModule =
    Module
        { moduleName = testSubMainModuleName
        , moduleSentences =
            [ importSentence testMetaModuleName
            , importSentence testObjectModuleName
            ]
        , moduleAttributes = Attributes [strictAttribute]
        }

mainModule :: Module ParsedSentence
mainModule =
    Module
        { moduleName = testMainModuleName
        , moduleSentences =
            [ importSentence testMetaModuleName
            , importSentence testSubMainModuleName
            ]
        , moduleAttributes = Attributes []
        }

testDefinition :: Definition ParsedSentence
testDefinition =
    Definition
        { definitionAttributes = Attributes [strictAttribute]
        , definitionModules =
            [ testObjectModule
            , testMetaModule
            , subMainModule
            , mainModule
            ]
        }

indexedModules ::
    Map ModuleName (VerifiedModule Attribute.Symbol)
indexedModules =
    assertRight $ verifyAndIndexDefinition Builtin.koreVerifiers testDefinition

testIndexedModule
    , testIndexedObjectModule ::
        VerifiedModule Attribute.Symbol
testIndexedModule =
    fromMaybe (error $ "Missing module: " ++ show testMainModuleName) $
        Map.lookup testMainModuleName indexedModules
testIndexedObjectModule =
    fromMaybe (error $ "Missing module: " ++ show testObjectModuleName) $
        Map.lookup testObjectModuleName indexedModules

test_resolvers :: [TestTree]
test_resolvers =
    [ testCase
        "object sort"
        ( assertEqual
            ""
            ( Right
                ( def :: Attribute.Sort
                , SentenceSort
                    { sentenceSortName = testId "s1"
                    , sentenceSortParameters = []
                    , sentenceSortAttributes = Attributes [strictAttribute]
                    }
                )
            )
            (resolveSort testIndexedModule (testId "s1" :: Id))
        )
    , testCase
        "meta sort"
        ( assertEqual
            ""
            ( Right
                ( def :: Attribute.Sort
                , SentenceSort
                    { sentenceSortName = stringMetaId
                    , sentenceSortParameters = []
                    , sentenceSortAttributes = Attributes []
                    }
                )
            )
            (resolveSort testIndexedModule stringMetaId)
        )
    , testCase
        "object symbol"
        ( assertEqual
            ""
            ( Right
                ( def{function = Function True}
                , SentenceSymbol
                    { sentenceSymbolAttributes =
                        Attributes [Attribute.functionAttribute]
                    , sentenceSymbolSymbol = sentenceSymbolSymbol objectA
                    , sentenceSymbolSorts = []
                    , sentenceSymbolResultSort = objectS1
                    }
                )
            )
            (resolveSymbol testIndexedModule (testId "a" :: Id))
        )
    , testCase
        "meta symbol"
        ( assertEqual
            ""
            ( Right
                ( def :: Attribute.Symbol
                , SentenceSymbol
                    { sentenceSymbolAttributes = Attributes []
                    , sentenceSymbolSymbol = sentenceSymbolSymbol metaA
                    , sentenceSymbolSorts = []
                    , sentenceSymbolResultSort = stringMetaSort
                    }
                )
            )
            (resolveSymbol testIndexedModule (testId "#a" :: Id))
        )
    , testCase
        "object alias"
        ( assertEqual
            ""
            ( Right
                ( def :: Attribute.Symbol
                , SentenceAlias
                    { sentenceAliasAttributes = Attributes []
                    , sentenceAliasAlias = sentenceAliasAlias objectB
                    , sentenceAliasSorts = []
                    , sentenceAliasLeftPattern =
                        Application
                            { applicationSymbolOrAlias =
                                SymbolOrAlias
                                    { symbolOrAliasConstructor =
                                        aliasConstructor
                                            (sentenceAliasAlias objectB)
                                    , symbolOrAliasParams =
                                        (<$>)
                                            SortVariableSort
                                            ( aliasParams $
                                                sentenceAliasAlias objectB
                                            )
                                    }
                            , applicationChildren = []
                            }
                    , sentenceAliasRightPattern = TermLike.mkTop objectS1
                    , sentenceAliasResultSort = objectS1
                    }
                )
            )
            (resolveAlias testIndexedModule (testId "b" :: Id))
        )
    , testCase
        "meta alias"
        ( assertEqual
            ""
            ( Right
                ( def :: Attribute.Symbol
                , SentenceAlias
                    { sentenceAliasAttributes = Attributes []
                    , sentenceAliasAlias = sentenceAliasAlias metaB
                    , sentenceAliasSorts = []
                    , sentenceAliasLeftPattern =
                        Application
                            { applicationSymbolOrAlias =
                                SymbolOrAlias
                                    { symbolOrAliasConstructor =
                                        aliasConstructor
                                            (sentenceAliasAlias metaB)
                                    , symbolOrAliasParams =
                                        (<$>)
                                            SortVariableSort
                                            ( aliasParams $
                                                sentenceAliasAlias metaB
                                            )
                                    }
                            , applicationChildren = []
                            }
                    , sentenceAliasRightPattern = TermLike.mkTop stringMetaSort
                    , sentenceAliasResultSort = stringMetaSort
                    }
                )
            )
            (resolveAlias testIndexedModule (testId "#b" :: Id))
        )
    , testCase
        "symbol getHeadApplicationSorts"
        ( assertEqual
            ""
            ApplicationSorts
                { applicationSortsOperands = []
                , applicationSortsResult = objectS1
                }
            ( getHeadApplicationSorts
                testIndexedModule
                (getSentenceSymbolOrAliasHead objectA [])
            )
        )
    , testCase
        "alias getHeadApplicationSorts"
        ( assertEqual
            ""
            ApplicationSorts
                { applicationSortsOperands = []
                , applicationSortsResult = objectS1
                }
            ( getHeadApplicationSorts
                testIndexedModule
                (getSentenceSymbolOrAliasHead objectB [])
            )
        )
    , testCase
        "sort indexed axioms"
        ( assertEqual
            ""
            (List.sortOn Data.Ord.Down [axiomA, axiomA'])
            ( fmap externalize . getIndexedSentence
                <$> indexedModuleAxioms testIndexedObjectModule
            )
        )
    ]
  where
    stringMetaId :: Id
    stringMetaId = stringMetaSortId

test_resolver_undefined_messages :: TestTree
test_resolver_undefined_messages =
    testGroup
        "each resolver has a standard failure message"
        [ resolveAlias `produces_` Error.noAlias
        , resolveSymbol `produces_` Error.noSymbol
        , resolveSort `produces_` Error.noSort
        ]
  where
    produces_ resolver formatter =
        checkLeftOf_ (run resolver) (checkWith formatter)
    run resolver =
        resolver testIndexedModule (testId "#anyOldId" :: Id)
    checkWith formatter =
        assertError_ ["(<test data>)"] $ formatter "#anyOldId"

-- TODO: Find out how to compose functions like the following
-- out of Test.Terse primitives. Is there a clean way to
-- do testcase nesting?

assertError_ :: [String] -> String -> Error a -> Assertion
assertError_ actualContext actualError expected =
    do
        assertEqual "errorContext" expectedContext actualContext
        assertEqual "errorError" expectedError actualError
  where
    Error
        { errorContext = expectedContext
        , errorError = expectedError
        } = expected

checkLeftOf_ :: Show r => Either l r -> (l -> Assertion) -> TestTree
checkLeftOf_ actual testBody =
    testCase "" $
        case actual of
            Left l ->
                testBody l
            Right unexpected ->
                assertFailure ("Unexpected Right " <> show unexpected)
