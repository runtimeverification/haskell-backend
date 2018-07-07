module Data.Kore.Step.AxiomPatternsTest where

import           Test.Tasty                                          (TestTree,
                                                                      testGroup)
import           Test.Tasty.HUnit                                    (assertEqual,
                                                                      testCase)

import qualified Data.Map                                            as Map
import           Data.Maybe                                          (fromMaybe)

import           Data.Kore.AST.Builders
import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore                                  (asKorePattern)
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.MLPatternsTest                        (extractPurePattern)
import           Data.Kore.AST.PureML
import           Data.Kore.AST.PureToKore
import           Data.Kore.AST.Sentence
import           Data.Kore.ASTVerifier.DefinitionVerifier            (AttributesVerification (..),
                                                                      verifyAndIndexDefinition)
import           Data.Kore.ASTVerifier.DefinitionVerifierTestHelpers
import           Data.Kore.Error
import           Data.Kore.IndexedModule.IndexedModule               (KoreIndexedModule)
import           Data.Kore.KoreHelpers                               (testId)
import           Data.Kore.Parser.ParserImpl
import           Data.Kore.Parser.ParserUtils
import           Data.Kore.Step.AxiomPatterns

axiomPatternsTests :: TestTree
axiomPatternsTests =
    testGroup
        "AxiomPatterns Tests"
        [ axiomPatternsUnitTests
        , axiomPatternsIntegrationTests
        ]

axiomPatternsUnitTests :: TestTree
axiomPatternsUnitTests =
    testGroup
        "AxiomPatterns Unit Tests"
        [ testCase "I1:AInt => I2:AInt"
            (assertEqual ""
                (Right AxiomPattern
                    { axiomPatternLeft = extractPurePattern varI1
                    , axiomPatternRight = extractPurePattern varI2
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
                    :: PureSentenceAxiom Object)
                )
            )
        , testCase "definition containing I1:AInt => I2:AInt"
            (assertEqual ""
                [AxiomPattern
                    { axiomPatternLeft = extractPurePattern varI1
                    , axiomPatternRight = extractPurePattern varI2
                    }
                ]
                ( koreIndexedModuleToAxiomPatterns Object
                $ extractIndexedModule "TEST"
                    (verifyAndIndexDefinition DoNotVerifyAttributes
                        (Definition
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
                                            :: PureSentenceAxiom Object)
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
                                            :: PureSentenceAxiom Object)
                                        , asSentence
                                            (SentenceSort
                                                { sentenceSortName =
                                                    testId "AInt"
                                                , sentenceSortParameters = []
                                                , sentenceSortAttributes =
                                                    Attributes []
                                                }
                                            ::KoreSentenceSort)
                                        , asSentence
                                            (SentenceSort
                                                { sentenceSortName =
                                                    testId "KItem"
                                                , sentenceSortParameters = []
                                                , sentenceSortAttributes =
                                                    Attributes []
                                                }
                                            ::KoreSentenceSort)
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
            )
        , testCase "\"a\" => \"b\""
            (assertEqual ""
                (koreFail "Unexpected non-Object pattern")
                ( koreSentenceToAxiomPattern Object
                $ asSentence
                    (SentenceAxiom
                        { sentenceAxiomPattern =
                            asKorePattern $ RewritesPattern Rewrites
                                { rewritesSort =
                                    sortVariableSort (SortVariableName "s")
                                , rewritesFirst =
                                    asKorePattern $
                                        StringLiteralPattern (StringLiteral "a")
                                , rewritesSecond =
                                    asKorePattern $
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
                    :: PureSentenceAxiom Object)
                )
            )
        ]

axiomPatternsIntegrationTests :: TestTree
axiomPatternsIntegrationTests =
    testGroup
        "AxiomPatterns Unit Tests"
        [ testCase "I1 <= I2 => I1 <=Int I2 (generated)"
            (assertEqual ""
                (Right AxiomPattern
                    { axiomPatternLeft = extractPurePattern $
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
                    , axiomPatternRight = extractPurePattern $
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

sortK, sortKItem, sortKCell, sortStateCell, sortTCell, sortState :: Sort Object
sortK = simpleSort (SortName "K")
sortKItem = simpleSort (SortName "KItem")

sortKCell = simpleSort (SortName "KCell")
sortStateCell = simpleSort (SortName "StateCell")
sortTCell = simpleSort (SortName "TCell")

sortState = simpleSort (SortName "State")

sortABool, sortAInt, sortAExp, sortBExp :: Sort Object
sortABool = simpleSort (SortName "ABool")
sortAInt = simpleSort (SortName "AInt")
sortAExp = simpleSort (SortName "AExp")
sortBExp = simpleSort (SortName "BExp")

sortParam :: String -> SortVariable Object
sortParam name = sortParameter Object name AstLocationTest

sortParamSort :: String -> Sort Object
sortParamSort = SortVariableSort . sortParam

symbolTCell, symbolStateCell, symbolKCell :: PureSentenceSymbol Object
symbolTCell =
    symbol_ "T" AstLocationTest
        [sortKCell, sortStateCell] sortTCell
-- symbol T{}(KCell{}, StateCell{}) : TCell{} []
symbolStateCell =
    symbol_ "Lbl'-LT-'state'-GT-'" AstLocationTest [sortState] sortStateCell
symbolKCell =
    symbol_ "k" AstLocationTest [sortK] sortKCell

symbolKSeq, symbolInj :: PureSentenceSymbol Object
symbolKSeq =
    symbol_ "kseq" AstLocationTest [sortKItem, sortK] sortK
symbolInj =
    parameterizedSymbol_ "inj" AstLocationTest
        [sortParam "From", sortParam "To"]
        [sortParamSort "From"]
        (sortParamSort "To")
-- symbol inj{From,To}(From) : To []

symbolLeqAExp :: PureSentenceSymbol Object
symbolLeqAExp =
    symbol_ "leqAExp"
        AstLocationTest [sortAExp, sortAExp] sortBExp

symbolLeqAInt :: PureSentenceSymbol Object
symbolLeqAInt =
    symbol_ "leqAInt"
        AstLocationTest [sortAInt, sortAInt] sortABool

varI1, varI2, varKRemainder, varStateCell :: CommonPurePatternStub Object
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
    :: String
    -> Either (Error a) (Map.Map ModuleName KoreIndexedModule)
    -> KoreIndexedModule
extractIndexedModule name eModules =
    case eModules of
        Left err -> error (printError err)
        Right modules -> fromMaybe
            (error ("Module " ++ name ++ " not found."))
            (Map.lookup (ModuleName name) modules)
