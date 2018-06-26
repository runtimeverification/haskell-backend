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
  "axiom{} \\and{TCell{}} (\n\
  \  \\top{TCell{}}(), \\and{TCell{}} (\n\
  \  \\top{TCell{}}(), \\rewrites{TCell{}}(\
    \Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(\
      \kseq{}(inj{BExp{}, KItem{}}(\
        \Lbl'Unds-LT-EqlsUndsUnds'IMP-SYNTAX'UndsUnds'AExp'Unds'AExp{}(\
          \inj{AInt{}, AExp{}}(VarI1:AInt{}),\
          \inj{AInt{}, AExp{}}(VarI2:AInt{})\
        \)\
      \),VarDotVar1:K{})),VarDotVar0:StateCell{}),\
    \Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(\
      \kseq{}(inj{ABool{}, KItem{}}(\
        \Lbl'Unds-LT-Eqls'AInt'UndsUnds'AINT'UndsUnds'AInt'Unds'AInt{}(\
          \VarI1:AInt{},\
          \VarI2:AInt{}\
        \)\
      \),VarDotVar1:K{})),VarDotVar0:StateCell{})\
    \)))\n\
\[]"

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
    symbol_ "Lbl'-LT-'T'-GT-'" AstLocationTest
        [sortKCell, sortStateCell] sortTCell
-- symbol Lbl'-LT-'T'-GT-'{}(KCell{}, StateCell{}) : TCell{} []
symbolStateCell =
    symbol_ "Lbl'-LT-'state'-GT-'" AstLocationTest [sortState] sortStateCell
symbolKCell =
    symbol_ "Lbl'-LT-'k'-GT-'" AstLocationTest [sortK] sortKCell

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
    symbol_ "Lbl'Unds-LT-EqlsUndsUnds'IMP-SYNTAX'UndsUnds'AExp'Unds'AExp"
        AstLocationTest [sortAExp, sortAExp] sortBExp

symbolLeqAInt :: PureSentenceSymbol Object
symbolLeqAInt =
    symbol_ "Lbl'Unds-LT-Eqls'AInt'UndsUnds'AINT'UndsUnds'AInt'Unds'AInt"
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

{-
  AxiomPattern {axiomPatternLeft = Fix (ApplicationPattern (Application {applicationSymbolOrAlias = SymbolOrAlias {symbolOrAliasConstructor = Id {getId = "Lbl'-LT-'T'-GT-'", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 39})}, symbolOrAliasParams = []}, applicationChildren = [Fix (ApplicationPattern (Application {applicationSymbolOrAlias = SymbolOrAlias {symbolOrAliasConstructor = Id {getId = "Lbl'-LT-'k'-GT-'", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3,
  column = 58})}, symbolOrAliasParams = []}, applicationChildren = [Fix (ApplicationPattern (Application {applicationSymbolOrAlias = SymbolOrAlias {symbolOrAliasConstructor = Id {getId = "kseq", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 77})}, symbolOrAliasParams = []}, applicationChildren = [Fix (ApplicationPattern (Application {applicationSymbolOrAlias = SymbolOrAlias {symbolOrAliasConstructor = Id {getId = "inj", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 84})}, symbolOrAliasParams = [SortActualSort (SortActual {sortActualName = Id {getId = "BExp", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 88})}, sortActualSorts = []}),SortActualSort (SortActual {sortActualName = Id
  {getId = "KItem", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 96})}, sortActualSorts = []})]}, applicationChildren = [Fix (ApplicationPattern (Application {applicationSymbolOrAlias = SymbolOrAlias {symbolOrAliasConstructor = Id {getId = "Lbl'Unds-LT-EqlsUndsUnds'IMP-SYNTAX'UndsUnds'AExp'Unds'AExp", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 105})}, symbolOrAliasParams = []}, applicationChildren = [Fix (ApplicationPattern (Application {applicationSymbolOrAlias = SymbolOrAlias {symbolOrAliasConstructor = Id {getId = "inj", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 167})}, symbolOrAliasParams = [SortActualSort (SortActual {sortActualName = Id {getId = "AInt", idLocation =
  AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 171})}, sortActualSorts = []}),SortActualSort (SortActual {sortActualName = Id {getId = "AExp", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 179})}, sortActualSorts = []})]}, applicationChildren = [Fix (VariablePattern (Variable {variableName = Id {getId = "VarI1", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 187})}, variableSort = SortActualSort (SortActual {sortActualName = Id {getId = "AInt", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 193})}, sortActualSorts = []})}))]})),Fix (ApplicationPattern (Application {applicationSymbolOrAlias = SymbolOrAlias {symbolOrAliasConstructor = Id {getId = "inj", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 201})}, symbolOrAliasParams = [SortActualSort (SortActual {sortActualName = Id {getId = "AInt", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 205})}, sortActualSorts = []}),SortActualSort (SortActual {sortActualName = Id {getId = "AExp", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 213})}, sortActualSorts = []})]}, applicationChildren = [Fix (VariablePattern (Variable {variableName = Id {getId = "VarI2", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 221})}, variableSort = SortActualSort (SortActual {sortActualName = Id {getId = "AInt", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 227})}, sortActualSorts = []})}))]}))]}))]})),Fix (VariablePattern (Variable {variableName = Id {getId = "VarDotVar1", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 237})}, variableSort = SortActualSort (SortActual {sortActualName = Id {getId = "K", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 248})}, sortActualSorts = []})}))]}))]})),Fix (VariablePattern (Variable {variableName = Id {getId = "VarDotVar0", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 254})}, variableSort = SortActualSort (SortActual {sortActualName = Id {getId = "StateCell", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 265})}, sortActualSorts = []})}))]})), axiomPatternRight = Fix (ApplicationPattern (Application {applicationSymbolOrAlias = SymbolOrAlias {symbolOrAliasConstructor = Id {getId = "Lbl'-LT-'T'-GT-'", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3,
  column = 278})}, symbolOrAliasParams = []}, applicationChildren = [Fix (ApplicationPattern (Application {applicationSymbolOrAlias = SymbolOrAlias {symbolOrAliasConstructor = Id {getId = "Lbl'-LT-'k'-GT-'", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 297})}, symbolOrAliasParams = []}, applicationChildren = [Fix (ApplicationPattern (Application {applicationSymbolOrAlias = SymbolOrAlias {symbolOrAliasConstructor = Id {getId = "kseq", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 316})}, symbolOrAliasParams = []}, applicationChildren = [Fix (ApplicationPattern (Application {applicationSymbolOrAlias = SymbolOrAlias {symbolOrAliasConstructor = Id {getId = "inj", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 323})}, symbolOrAliasParams = [SortActualSort (SortActual {sortActualName = Id {getId = "ABool", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 327})}, sortActualSorts = []}),SortActualSort (SortActual {sortActualName = Id {getId = "KItem", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 336})}, sortActualSorts = []})]}, applicationChildren = [Fix (ApplicationPattern (Application {applicationSymbolOrAlias = SymbolOrAlias {symbolOrAliasConstructor = Id {getId = "Lbl'Unds-LT-Eqls'AInt'UndsUnds'AINT'UndsUnds'AInt'Unds'AInt", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 345})}, symbolOrAliasParams = []}, applicationChildren = [Fix (VariablePattern (Variable {variableName = Id {getId = "VarI1", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 407})}, variableSort = SortActualSort (SortActual {sortActualName = Id {getId = "AInt", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 413})}, sortActualSorts = []})})),Fix (VariablePattern (Variable {variableName = Id {getId = "VarI2", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 420})}, variableSort = SortActualSort (SortActual {sortActualName = Id {getId = "AInt", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 426})}, sortActualSorts = []})}))]}))]})),Fix (VariablePattern (Variable {variableName = Id {getId = "VarDotVar1", idLocation = AstLocationFile
  (FileLocation {fileName = "<test-string>", line = 3, column = 435})}, variableSort = SortActualSort (SortActual {sortActualName = Id {getId = "K", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 446})}, sortActualSorts = []})}))]}))]})),Fix (VariablePattern (Variable {variableName = Id {getId = "VarDotVar0", idLocation = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 452})}, variableSort = SortActualSort (SortActual {sortActualName = Id {getId = "StateCell", idLocation
  = AstLocationFile (FileLocation {fileName = "<test-string>", line = 3, column = 463})}, sortActualSorts = []})}))]}))}
-}

testAxiom1 :: KoreSentence
testAxiom1 = case parseAxiom testAxiomString1 of
    Left err -> error err
    Right ax -> ax

parseAxiom :: String -> Either String KoreSentence
parseAxiom = parseOnly (koreSentenceParser <* endOfInput) "<test-string>"
