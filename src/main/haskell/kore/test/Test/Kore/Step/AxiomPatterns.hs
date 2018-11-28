module Test.Kore.Step.AxiomPatterns (test_axiomPatterns) where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import           Data.Default
import qualified Data.Map as Map
import           Data.Maybe
                 ( fromMaybe )
import           Data.Proxy
                 ( Proxy (..) )
import           Data.Text
                 ( Text )
import qualified Data.Text as Text

import           Kore.AST.Builders
import           Kore.AST.Kore
import           Kore.AST.Pure
import           Kore.AST.PureToKore
import           Kore.AST.Sentence
import           Kore.ASTUtils.SmartPatterns
import           Kore.ASTVerifier.DefinitionVerifier
                 ( AttributesVerification (..), verifyAndIndexDefinition )
import qualified Kore.Attribute.Null as Attribute
import qualified Kore.Builtin as Builtin
import qualified Kore.Domain.Builtin as Domain
import           Kore.Error
import           Kore.IndexedModule.IndexedModule
                 ( KoreIndexedModule )
import           Kore.Parser.ParserImpl
import           Kore.Parser.ParserUtils
import           Kore.Predicate.Predicate
                 ( wrapPredicate )
import           Kore.Step.AxiomPatterns
import           Kore.Step.Pattern

import Test.Kore
       ( sortVariableSort, testId )
import Test.Kore.AST.MLPatterns
       ( extractPurePattern )
import Test.Kore.ASTVerifier.DefinitionVerifier

test_axiomPatterns :: [TestTree]
test_axiomPatterns =
    [ axiomPatternsUnitTests
    , axiomPatternsIntegrationTests
    ]

axiomPatternsUnitTests :: TestTree
axiomPatternsUnitTests =
    testGroup
        "AxiomPatterns Unit Tests"
        [ testCase "I1:AInt => I2:AInt"
            (assertEqual ""
                (Right $ RewriteAxiomPattern $ RewriteRule RulePattern
                    { left = extractPurePattern varI1
                    , right = extractPurePattern varI2
                    , requires = wrapPredicate topAInt
                    , attributes = def
                    }
                )
                ( koreSentenceToAxiomPattern Object
                $ asSentence $ axiomSentencePureToKore
                    (axiom_
                        (and_ top_
                            (and_ top_
                                (rewrites_ varI1 varI2)
                            )
                        )
                    :: PureSentenceAxiom Object Domain.Builtin)
                )
            )
        , testCase "definition containing I1:AInt => I2:AInt"
            (assertEqual ""
                [ RewriteRule RulePattern
                    { left = extractPurePattern varI1
                    , right = extractPurePattern varI2
                    , requires = wrapPredicate topAInt
                    , attributes = def
                    }
                ]
                ( extractRewriteAxioms Object
                $ extractIndexedModule "TEST"
                    (verifyAndIndexDefinition
                        DoNotVerifyAttributes
                        Builtin.koreVerifiers
                        Definition
                            { definitionAttributes = Attributes []
                            , definitionModules =
                                [ Module
                                    { moduleName = ModuleName "TEST"
                                    , moduleSentences =
                                        [ asSentence $ axiomSentencePureToKore
                                            (axiom_
                                                (and_ top_
                                                    (and_ top_
                                                        (rewrites_ varI1 varI2)
                                                    )
                                                )
                                            :: PureSentenceAxiom Object Domain.Builtin)
                                        , asSentence $ axiomSentencePureToKore
                                            (axiom_
                                                (and_ top_
                                                    (and_ top_
                                                        (applyPS symbolInj
                                                            [sortAInt
                                                            , sortKItem
                                                            ]
                                                            [rewrites_
                                                                varI1
                                                                varI2
                                                            ]
                                                        )
                                                    )
                                                )
                                            :: PureSentenceAxiom Object Domain.Builtin)
                                        , asSentence
                                            (SentenceSort
                                                { sentenceSortName =
                                                    testId "AInt"
                                                , sentenceSortParameters = []
                                                , sentenceSortAttributes =
                                                    Attributes []
                                                }
                                            ::KoreSentenceSort Object)
                                        , asSentence
                                            (SentenceSort
                                                { sentenceSortName =
                                                    testId "KItem"
                                                , sentenceSortParameters = []
                                                , sentenceSortAttributes =
                                                    Attributes []
                                                }
                                            ::KoreSentenceSort Object)
                                        , sentencePureToKore $
                                            asSentence symbolInj
                                        ]
                                    , moduleAttributes = Attributes []
                                    }
                                ]
                            }
                    )
                )
            )
        , testCase "\"a\" => \"b\""
            (assertEqual ""
                (koreFail "Unexpected meta-level pattern")
                ( koreSentenceToAxiomPattern Object
                $ asSentence
                    (SentenceAxiom
                        { sentenceAxiomPattern =
                            asCommonKorePattern $ RewritesPattern Rewrites
                                { rewritesSort =
                                    sortVariableSort "s"
                                , rewritesFirst =
                                    asCommonKorePattern $
                                        StringLiteralPattern (StringLiteral "a")
                                , rewritesSecond =
                                    asCommonKorePattern $
                                        StringLiteralPattern (StringLiteral "b")
                                }
                        , sentenceAxiomParameters = []
                        , sentenceAxiomAttributes = Attributes []
                        }
                    :: KoreSentenceAxiom)
                )
            )
        , testCase "(I1:AInt => I2:AInt)::KItem"
            (assertEqual ""
                (koreFail "Unsupported pattern type in axiom")
                (koreSentenceToAxiomPattern Object
                $ asSentence $ axiomSentencePureToKore
                    (axiom_
                        (and_ top_
                            (and_ top_
                                (applyPS symbolInj [sortAInt, sortKItem]
                                    [rewrites_ varI1 varI2]
                                )
                            )
                        )
                    :: PureSentenceAxiom Object Domain.Builtin)
                )
            )
        ]

axiomPatternsIntegrationTests :: TestTree
axiomPatternsIntegrationTests =
    testGroup
        "AxiomPatterns Unit Tests"
        [ testCase "I1 <= I2 => I1 <=Int I2 (generated)"
            (assertEqual ""
                (Right $ RewriteAxiomPattern $ RewriteRule RulePattern
                    { left = extractPurePattern $
                        applyS symbolTCell
                          [ applyS symbolKCell
                              [ applyS symbolKSeq
                                  [ applyPS symbolInj [sortBExp, sortKItem]
                                      [ applyS symbolLeqAExp
                                          [ applyPS symbolInj
                                              [sortAInt, sortAExp] [varI1]
                                          , applyPS symbolInj
                                              [sortAInt, sortAExp] [varI2]
                                          ]
                                      ]
                                  , varKRemainder
                                  ]
                              ]
                          , varStateCell
                          ]
                    , right = extractPurePattern $
                        applyS symbolTCell
                          [ applyS symbolKCell
                              [ applyS symbolKSeq
                                  [ applyPS symbolInj [sortABool, sortKItem]
                                      [ applyS symbolLeqAInt [ varI1, varI2 ] ]
                                  , varKRemainder
                                  ]
                              ]
                          , varStateCell
                          ]
                    , requires = wrapPredicate topTCell
                    , attributes = def
                    }
                )
                (koreSentenceToAxiomPattern Object =<< parseAxiom
                    "axiom{}\\and{TCell{}}(\n\
                    \    \\top{TCell{}}(),\n\
                    \    \\and{TCell{}}(\n\
                    \        \\top{TCell{}}(),\n\
                    \        \\rewrites{TCell{}}(\n\
                    \            T{}(\n\
                    \                k{}(\n\
                    \                    kseq{}(\n\
                    \                        inj{BExp{}, KItem{}}(\n\
                    \                            leqAExp{}(\n\
                    \                                inj{AInt{}, AExp{}}(\n\
                    \                                    VarI1:AInt{}\n\
                    \                                ),\n\
                    \                                inj{AInt{}, AExp{}}(\n\
                    \                                    VarI2:AInt{}\n\
                    \                                )\n\
                    \                            )\n\
                    \                        ),\n\
                    \                        VarDotVar1:K{}\n\
                    \                    )\n\
                    \                ),\n\
                    \                VarDotVar0:StateCell{}\n\
                    \            ),\n\
                    \            T{}(\n\
                    \                k{}(\n\
                    \                    kseq{}(\n\
                    \                        inj{ABool{}, KItem{}}(\n\
                    \                            leqAInt{}(\n\
                    \                                VarI1:AInt{},\n\
                    \                                VarI2:AInt{})\n\
                    \                        ),\n\
                    \                        VarDotVar1:K{}\n\
                    \                    )\n\
                    \                ),\n\
                    \                VarDotVar0:StateCell{}\n\
                    \            )\n\
                    \        )\n\
                    \    )\n\
                    \)[]"
                )
            )
        ]

sortK, sortKItem, sortKCell, sortStateCell, sortTCell :: Sort Object
sortK = simpleSort (SortName "K")
sortKItem = simpleSort (SortName "KItem")

sortKCell = simpleSort (SortName "KCell")
sortStateCell = simpleSort (SortName "StateCell")
sortTCell = simpleSort (SortName "TCell")

sortABool, sortAInt, sortAExp, sortBExp :: Sort Object
sortABool = simpleSort (SortName "ABool")
sortAInt = simpleSort (SortName "AInt")
sortAExp = simpleSort (SortName "AExp")
sortBExp = simpleSort (SortName "BExp")

sortParam :: Text -> SortVariable Object
sortParam name = sortParameter Proxy name AstLocationTest

sortParamSort :: Text -> Sort Object
sortParamSort = SortVariableSort . sortParam

symbolTCell, symbolKCell :: PureSentenceSymbol Object Domain.Builtin
symbolTCell =
    symbol_ "T" AstLocationTest
        [sortKCell, sortStateCell] sortTCell
-- symbol T{}(KCell{}, StateCell{}) : TCell{} []
symbolKCell =
    symbol_ "k" AstLocationTest [sortK] sortKCell

symbolKSeq, symbolInj :: PureSentenceSymbol Object Domain.Builtin
symbolKSeq =
    symbol_ "kseq" AstLocationTest [sortKItem, sortK] sortK
symbolInj =
    parameterizedSymbol_ "inj" AstLocationTest
        [sortParam "From", sortParam "To"]
        [sortParamSort "From"]
        (sortParamSort "To")
-- symbol inj{From,To}(From) : To []

symbolLeqAExp :: PureSentenceSymbol Object Domain.Builtin
symbolLeqAExp =
    symbol_ "leqAExp"
        AstLocationTest [sortAExp, sortAExp] sortBExp

symbolLeqAInt :: PureSentenceSymbol Object Domain.Builtin
symbolLeqAInt =
    symbol_ "leqAInt"
        AstLocationTest [sortAInt, sortAInt] sortABool

varI1, varI2, varKRemainder, varStateCell :: CommonPurePatternStub Object Domain.Builtin ()
varI1 = parameterizedVariable_ sortAInt "VarI1" AstLocationTest
varI2 = parameterizedVariable_ sortAInt "VarI2" AstLocationTest
varKRemainder = parameterizedVariable_ sortK "VarDotVar1" AstLocationTest
varStateCell = parameterizedVariable_ sortStateCell "VarDotVar0" AstLocationTest

parseAxiom :: String -> Either (Error a) KoreSentence
parseAxiom str =
    case parseOnly (koreSentenceParser <* endOfInput) "<test-string>" str of
        Left err  -> koreFail err
        Right sen -> return sen

extractIndexedModule
    :: Text
    -> Either (Error a) (Map.Map ModuleName (KoreIndexedModule Attribute.Null))
    -> KoreIndexedModule Attribute.Null
extractIndexedModule name eModules =
    case eModules of
        Left err -> error (printError err)
        Right modules -> fromMaybe
            (error ("Module " ++ Text.unpack name ++ " not found."))
            (Map.lookup (ModuleName name) modules)

topAInt :: CommonStepPattern Object
topAInt = Top_ sortAInt

topTCell :: CommonStepPattern Object
topTCell = Top_ sortTCell
