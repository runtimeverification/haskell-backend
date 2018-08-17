module Test.Kore.Step.AxiomPatterns (test_axiomPatterns) where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import qualified Data.Map as Map
import           Data.Maybe
                 ( fromMaybe )

import Kore.AST.Builders
import Kore.AST.Common
import Kore.AST.Kore
       ( asKorePattern )
import Kore.AST.MetaOrObject
import Kore.AST.PureML
import Kore.AST.PureToKore
import Kore.AST.Sentence
import Kore.ASTUtils.SmartPatterns
import Kore.ASTVerifier.DefinitionVerifier
       ( AttributesVerification (..), verifyAndIndexDefinition )
import qualified Kore.Builtin as Builtin
import Kore.Error
import Kore.IndexedModule.IndexedModule
       ( KoreIndexedModule )
import Kore.Implicit.Attributes
import Kore.Parser.ParserImpl
import Kore.Parser.ParserUtils
import Kore.Predicate.Predicate ( wrapPredicate )
import Kore.Step.AxiomPatterns

import Test.Kore
       ( testId )
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
                (Right AxiomPattern
                    { axiomPatternLeft = extractPurePattern varI1
                    , axiomPatternRight = extractPurePattern varI2
                    , axiomPatternRequires = wrapPredicate topAInt
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
                    , axiomPatternRequires = wrapPredicate topAInt
                    }
                ]
                ( koreIndexedModuleToAxiomPatterns Object
                $ extractIndexedModule "TEST"
                    (verifyAndIndexDefinition
                        DoNotVerifyAttributes
                        Builtin.koreBuiltins
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
                    , axiomPatternRequires = wrapPredicate topTCell
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

sortParam :: String -> SortVariable Object
sortParam name = sortParameter Object name AstLocationTest

sortParamSort :: String -> Sort Object
sortParamSort = SortVariableSort . sortParam

symbolTCell, symbolKCell :: PureSentenceSymbol Object
symbolTCell =
    symbol_ "T" AstLocationTest
        [sortKCell, sortStateCell] sortTCell
-- symbol T{}(KCell{}, StateCell{}) : TCell{} []
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
    -> Either (Error a) (Map.Map ModuleName (KoreIndexedModule ImplicitAttributes))
    -> KoreIndexedModule ImplicitAttributes
extractIndexedModule name eModules =
    case eModules of
        Left err -> error (printError err)
        Right modules -> fromMaybe
            (error ("Module " ++ name ++ " not found."))
            (Map.lookup (ModuleName name) modules)

topAInt :: CommonPurePattern Object
topAInt = Top_ sortAInt

topTCell :: CommonPurePattern Object
topTCell = Top_ sortTCell
