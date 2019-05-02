module Test.Kore.IndexedModule.Resolvers where

import Test.Tasty
import Test.Tasty.HUnit

import           Data.Default
import qualified Data.List as List
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import qualified Data.Set as Set

import           Kore.ASTHelpers
import           Kore.ASTVerifier.DefinitionVerifier
import qualified Kore.Attribute.Null as Attribute
import qualified Kore.Attribute.Pattern as Attribute
import qualified Kore.Attribute.Sort as Attribute
import qualified Kore.Builtin as Builtin
import           Kore.Error
import           Kore.IndexedModule.Error as Error
import           Kore.IndexedModule.IndexedModule
import           Kore.IndexedModule.Resolvers
import           Kore.Internal.TermLike hiding
                 ( freeVariables )
import           Kore.Syntax
import           Kore.Syntax.Definition
import           Kore.Syntax.PatternF
                 ( groundHead )
import qualified Kore.Verified as Verified

import Test.Kore
import Test.Kore.ASTVerifier.DefinitionVerifier

objectS1 :: Sort
objectS1 = simpleSort (SortName "s1")

objectA :: SentenceSymbol (TermLike Variable)
objectA = mkSymbol_ (testId "a") [] objectS1

-- Two variations on a constructor axiom for 'objectA'.
axiomA, axiomA' :: SentenceAxiom (TermLike Variable)
axiomA = mkAxiom_ $ applySymbol_ objectA []
axiomA' =
    mkAxiom [sortVariableR]
    $ mkForall x
    $ mkEquals sortR (mkVar x) (applySymbol_ objectA [])
  where
    x = varS "x" objectS1
    sortVariableR = SortVariable (testId "R")
    sortR = SortVariableSort sortVariableR

objectB :: SentenceAlias (TermLike Variable)
objectB = mkAlias_ (testId "b") objectS1 [] $ mkTop objectS1

metaA :: SentenceSymbol (TermLike Variable)
metaA = mkSymbol_ (testId "#a") [] stringMetaSort

metaB :: SentenceAlias (TermLike Variable)
metaB = mkAlias_ (testId "#b") stringMetaSort [] $ mkTop stringMetaSort

testObjectModuleName :: ModuleName
testObjectModuleName = ModuleName "TEST-OBJECT-MODULE"

testMetaModuleName :: ModuleName
testMetaModuleName = ModuleName "TEST-META-MODULE"

testSubMainModuleName :: ModuleName
testSubMainModuleName = ModuleName "TEST-SUB-MAIN-MODULE"

testMainModuleName :: ModuleName
testMainModuleName = ModuleName "TEST-MAIN-MODULE"

strictAttribute :: ParsedPattern
strictAttribute =
    (asParsedPattern . ApplicationF)
        Application
            { applicationSymbolOrAlias = groundHead "strict" AstLocationTest
            , applicationChildren = []
            }

testObjectModule :: Module Verified.Sentence
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

testMetaModule :: Module Verified.Sentence
testMetaModule =
    Module
        { moduleName = testMetaModuleName
        , moduleSentences =
            [ asSentence metaA
            , asSentence metaB
            ]
        , moduleAttributes = Attributes []
        }

subMainModule :: Module Verified.Sentence
subMainModule =
    Module
        { moduleName = testSubMainModuleName
        , moduleSentences =
            [ importSentence testMetaModuleName
            , importSentence testObjectModuleName
            ]
        , moduleAttributes = Attributes [strictAttribute]
        }

mainModule :: Module Verified.Sentence
mainModule =
    Module
        { moduleName = testMainModuleName
        , moduleSentences =
            [ importSentence testMetaModuleName
            , importSentence testSubMainModuleName
            ]
        , moduleAttributes = Attributes []
        }


testDefinition :: Definition Verified.Sentence
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

indexedModules :: Map ModuleName (VerifiedModule Attribute.Null Attribute.Null)
Right indexedModules =
    verifyAndIndexDefinition
        DoNotVerifyAttributes
        Builtin.koreVerifiers
        (eraseSentenceAnnotations <$> testDefinition)

testIndexedModule, testIndexedObjectModule
    :: VerifiedModule Attribute.Null Attribute.Null
Just testIndexedModule = Map.lookup testMainModuleName indexedModules
Just testIndexedObjectModule = Map.lookup testObjectModuleName indexedModules

test_resolvers :: [TestTree]
test_resolvers =
    [ testCase "object sort"
        (assertEqual ""
            (Right (def :: Attribute.Sort, SentenceSort
                { sentenceSortName = testId "s1"
                , sentenceSortParameters = []
                , sentenceSortAttributes = Attributes [strictAttribute]
                })
            )
            (resolveSort testIndexedModule (testId "s1" :: Id))
        )
    , testCase "meta sort"
        (assertEqual ""
            (Right (def :: Attribute.Sort, SentenceSort
                { sentenceSortName = charMetaId
                , sentenceSortParameters = []
                , sentenceSortAttributes = Attributes []
                }
            ))
            (resolveSort testIndexedModule charMetaId)
        )
    , testCase "object symbol"
        (assertEqual ""
            (Right (def :: Attribute.Null, SentenceSymbol
                { sentenceSymbolAttributes = Attributes []
                , sentenceSymbolSymbol = sentenceSymbolSymbol objectA
                , sentenceSymbolSorts = []
                , sentenceSymbolResultSort = objectS1
                }
            ))
            (resolveSymbol testIndexedModule (testId "a" :: Id))
        )
    , testCase "meta symbol"
        (assertEqual ""
            (Right (def :: Attribute.Null, SentenceSymbol
                { sentenceSymbolAttributes = Attributes []
                , sentenceSymbolSymbol = sentenceSymbolSymbol metaA
                , sentenceSymbolSorts = []
                , sentenceSymbolResultSort = stringMetaSort
                }
            ))
            (resolveSymbol testIndexedModule (testId "#a" :: Id))
        )
    , testCase "object alias"
        (assertEqual ""
            (Right
                ( def :: Attribute.Null
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
                                            (aliasParams
                                                $ sentenceAliasAlias objectB
                                            )
                                    }
                            , applicationChildren = []
                            }
                    , sentenceAliasRightPattern =
                        let
                            valid =
                                Attribute.Pattern
                                    { patternSort = objectS1
                                    , freeVariables = Set.empty
                                    }
                            top' = TopF Top { topSort = objectS1 }
                        in
                            asPurePattern (valid :< top')
                    , sentenceAliasResultSort = objectS1
                    }
                )
            )
            (resolveAlias testIndexedModule (testId "b" :: Id))
        )
    , testCase "meta alias"
        (assertEqual ""
            (Right (def :: Attribute.Null, SentenceAlias
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
                                        (aliasParams
                                            $ sentenceAliasAlias metaB
                                        )
                                }
                        , applicationChildren = []
                        }
                , sentenceAliasRightPattern =
                    let
                        valid = Attribute.Pattern { patternSort, freeVariables }
                          where
                            patternSort = stringMetaSort
                            freeVariables = Set.empty
                        top' = TopF Top { topSort = stringMetaSort }
                    in
                        asPurePattern (valid :< top')
                , sentenceAliasResultSort = stringMetaSort
                }
            ))
            (resolveAlias testIndexedModule (testId "#b" :: Id))
        )
    , testCase "symbol getHeadApplicationSorts"
        (assertEqual ""
            ApplicationSorts
                { applicationSortsOperands = []
                , applicationSortsResult = objectS1
                }
            (getHeadApplicationSorts
                testIndexedModule
                (getSentenceSymbolOrAliasHead objectA [])
            )
        )
    , testCase "alias getHeadApplicationSorts"
        (assertEqual ""
            ApplicationSorts
                { applicationSortsOperands = []
                , applicationSortsResult = objectS1
                }
            (getHeadApplicationSorts
                testIndexedModule
                (getSentenceSymbolOrAliasHead objectB [])
            )
        )
    , testCase "sort indexed axioms"
        (assertEqual ""
            (reverse $ List.sort [axiomA, axiomA'])
            (getIndexedSentence <$> indexedModuleAxioms testIndexedObjectModule)
        )
    ]
  where
    charMetaId :: Id
    charMetaId = charMetaSortId


test_resolver_undefined_messages :: TestTree
test_resolver_undefined_messages =
    testGroup "each resolver has a standard failure message"
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
assertError_ actualContext actualError expected
  = do
        assertEqual "errorContext" expectedContext  actualContext
        assertEqual "errorError"  expectedError  actualError
  where
    Error { errorContext = expectedContext
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
