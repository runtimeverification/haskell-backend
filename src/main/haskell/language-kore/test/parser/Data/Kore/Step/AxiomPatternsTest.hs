module Data.Kore.Step.AxiomPatternsTest where

import           Test.Tasty                                          (TestTree,
                                                                      testGroup)
import           Test.Tasty.HUnit                                    (assertEqual,
                                                                      testCase)

import           Data.Kore.AST.Builders
import           Data.Kore.AST.Common
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.MLPatternsTest                        (extractPurePattern)
import           Data.Kore.AST.PureML
import           Data.Kore.AST.Sentence
import           Data.Kore.ASTVerifier.DefinitionVerifierTestHelpers
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
        []

axiomPatternsIntegrationTests :: TestTree
axiomPatternsIntegrationTests =
    testGroup
        "AxiomPatterns Unit Tests"
        [ testCase "I1 <= I2 => I1 <=Int I2"
            (assertEqual
                ""
                (Right expectedAxiomPattern1)
                (koreSentenceToAxiomPattern Object testAxiom1)
            )

        ]

testAxiomString1 :: String
testAxiomString1 =
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
    \                                inj{AInt{}, AExp{}}(VarI1:AInt{}),\n\
    \                                inj{AInt{}, AExp{}}(VarI2:AInt{})\n\
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
    \                            leqAInt{}(VarI1:AInt{}, VarI2:AInt{})\n\
    \                        ),\n\
    \                        VarDotVar1:K{}\n\
    \                    )\n\
    \                ),\n\
    \                VarDotVar0:StateCell{}\n\
    \            )\n\
    \        )\n\
    \    )\n\
    \)[]"

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

expectedAxiomPattern1 :: AxiomPattern Object
expectedAxiomPattern1 = AxiomPattern
    { axiomPatternLeft = extractPurePattern $
        applyS symbolTCell
          [ applyS symbolKCell
              [ applyS symbolKSeq
                  [ applyPS symbolInj [sortBExp, sortKItem]
                      [ applyS symbolLeqAExp
                          [ applyPS symbolInj [sortAInt, sortAExp] [varI1]
                          , applyPS symbolInj [sortAInt, sortAExp] [varI2]
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

testAxiom1 :: KoreSentence
testAxiom1 = case parseAxiom testAxiomString1 of
    Left err -> error err
    Right ax -> ax

parseAxiom :: String -> Either String KoreSentence
parseAxiom = parseOnly (koreSentenceParser <* endOfInput) "<test-string>"
