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
import           Kore.AST.Valid
import           Kore.ASTVerifier.DefinitionVerifier
                 ( AttributesVerification (..), verifyAndIndexDefinition )
import qualified Kore.Attribute.Null as Attribute
import qualified Kore.Builtin as Builtin
import           Kore.Error
import           Kore.IndexedModule.IndexedModule
                 ( VerifiedModule )
import           Kore.Parser.ParserImpl
import           Kore.Parser.ParserUtils
import           Kore.Predicate.Predicate
                 ( wrapPredicate )
import           Kore.Step.AxiomPatterns
import           Kore.Step.Pattern

import Test.Kore
       ( testId )
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
                    { left = varI1
                    , right = varI2
                    , requires = wrapPredicate (mkTop sortAInt)
                    , attributes = def
                    }
                )
                ( koreSentenceToAxiomPattern Object
                $ asKoreAxiomSentence $ axiomSentencePureToKore
                    (mkAxiom_
                        (mkAnd
                            mkTop_
                            (mkAnd
                                mkTop_
                                (mkRewrites varI1 varI2)
                            )
                        )
                    )
                )
            )
        ,   let
                axiom1 :: VerifiedKoreSentence
                axiom1 =
                    (asKoreAxiomSentence . axiomSentencePureToKore)
                        (mkAxiom_
                            (mkAnd
                                mkTop_
                                (mkAnd mkTop_ (mkRewrites varI1 varI2))
                            )
                        )
                axiom2 :: VerifiedKoreSentence
                axiom2 =
                    (asKoreAxiomSentence . axiomSentencePureToKore)
                        (mkAxiom_
                            (mkAnd
                                mkTop_
                                (mkAnd
                                    mkTop_
                                    (applyInj
                                        sortKItem
                                        (mkRewrites varI1 varI2)
                                    )
                                )
                            )
                        )
                moduleTest =
                    Module
                        { moduleName = ModuleName "TEST"
                        , moduleSentences =
                            map
                                eraseUnifiedSentenceAnnotations
                                [ axiom1
                                , axiom2
                                , sortSentenceAInt
                                , sortSentenceKItem
                                , sentencePureToKore symbolSentenceInj
                                ]
                        , moduleAttributes = Attributes []
                        }
                indexedDefinition =
                    verifyAndIndexDefinition
                        DoNotVerifyAttributes
                        Builtin.koreVerifiers
                        Definition
                            { definitionAttributes = Attributes []
                            , definitionModules = [ moduleTest ]
                            }
            in
                testCase "definition containing I1:AInt => I2:AInt"
                $ assertEqual ""
                    [ RewriteRule RulePattern
                        { left = varI1
                        , right = varI2
                        , requires = wrapPredicate (mkTop sortAInt)
                        , attributes = def
                        }
                    ]
                    (extractRewriteAxioms Object
                        (extractIndexedModule "TEST" indexedDefinition)
                    )
        , testCase "(I1:AInt => I2:AInt)::KItem"
            (assertEqual ""
                (koreFail "Unsupported pattern type in axiom")
                (koreSentenceToAxiomPattern Object
                $ asKoreAxiomSentence $ axiomSentencePureToKore
                    (mkAxiom_
                        (mkAnd
                            mkTop_
                            (mkAnd
                                mkTop_
                                (applySymbol
                                    symbolInj
                                    [sortAInt, sortKItem]
                                    [mkRewrites varI1 varI2]
                                )
                            )
                        )
                    )
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
                    { left =
                        applyTCell
                            (applyKCell
                                (applyKSeq
                                    (applyInj sortKItem
                                        (applyLeqAExp
                                            (applyInj sortAExp varI1)
                                            (applyInj sortAExp varI2)
                                        )
                                    )
                                    varKRemainder
                                )
                            )
                            varStateCell
                    , right =
                        applyTCell
                            (applyKCell
                                (applyKSeq
                                    (applyInj
                                        sortKItem
                                        (applyLeqAInt varI1 varI2)
                                    )
                                    varKRemainder
                                )
                            )
                            varStateCell
                    , requires = wrapPredicate (mkTop sortTCell)
                    , attributes = def
                    }
                )
                (do
                    parsed <-
                        parseAxiom
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
                    let valid = UnifiedObject Valid { patternSort = sortTCell }
                    koreSentenceToAxiomPattern Object ((<$) valid <$> parsed)
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

sortSentenceAInt :: VerifiedKoreSentence
sortSentenceAInt =
    sentencePureToKore (asSentence sentence)
  where
    sentence :: SentenceSort Object (CommonStepPattern Object)
    sentence =
        SentenceSort
            { sentenceSortName = testId "AInt"
            , sentenceSortParameters = []
            , sentenceSortAttributes = Attributes []
            }

sortSentenceKItem :: VerifiedKoreSentence
sortSentenceKItem =
    sentencePureToKore (asSentence sentence)
  where
    sentence :: SentenceSort Object (CommonStepPattern Object)
    sentence =
        SentenceSort
            { sentenceSortName = testId "KItem"
            , sentenceSortParameters = []
            , sentenceSortAttributes = Attributes []
            }

sortParam :: Text -> SortVariable Object
sortParam name = sortParameter Proxy name AstLocationTest

sortParamSort :: Text -> Sort Object
sortParamSort = SortVariableSort . sortParam

symbolTCell, symbolKCell :: SentenceSymbol Object (CommonStepPattern Object)
symbolTCell = mkSymbol_ (testId "T") [sortKCell, sortStateCell] sortTCell
-- symbol T{}(KCell{}, StateCell{}) : TCell{} []
applyTCell
    :: CommonStepPattern Object  -- ^ K cell
    -> CommonStepPattern Object  -- ^ State cell
    -> CommonStepPattern Object
applyTCell kCell stateCell =
    applySymbol_ symbolTCell [kCell, stateCell]

symbolKCell = mkSymbol_ (testId "k") [sortK] sortKCell
applyKCell
    :: CommonStepPattern Object
    -> CommonStepPattern Object
applyKCell child = applySymbol_ symbolKCell [child]

symbolKSeq, symbolInj :: SentenceSymbol Object (CommonStepPattern Object)
symbolKSeq = mkSymbol_ (testId "kseq") [sortKItem, sortK] sortK

symbolInj =
    mkSymbol
        (testId "inj")
        [sortParam "From", sortParam "To"]
        [sortParamSort "From"]
        (sortParamSort "To")

applyKSeq
    :: CommonStepPattern Object  -- ^ head
    -> CommonStepPattern Object  -- ^ tail
    -> CommonStepPattern Object
applyKSeq kHead kTail =
    applySymbol_ symbolKSeq [kHead, kTail]

applyInj
    :: Sort Object  -- ^ destination sort
    -> CommonStepPattern Object  -- ^ argument
    -> CommonStepPattern Object
applyInj sortTo child =
    applySymbol symbolInj [sortFrom, sortTo] [child]
  where
    Valid { patternSort = sortFrom } = extract child

symbolSentenceInj
    :: Sentence Object (SortVariable Object) (CommonStepPattern Object)
symbolSentenceInj = asSentence symbolInj
-- symbol inj{From,To}(From) : To []

symbolLeqAExp :: SentenceSymbol Object (CommonStepPattern Object)
symbolLeqAExp = mkSymbol_ (testId "leqAExp") [sortAExp, sortAExp] sortBExp

applyLeqAExp
    :: CommonStepPattern Object
    -> CommonStepPattern Object
    -> CommonStepPattern Object
applyLeqAExp child1 child2 =
    applySymbol_ symbolLeqAExp [child1, child2]

symbolLeqAInt :: SentenceSymbol Object (CommonStepPattern Object)
symbolLeqAInt = mkSymbol_ (testId "leqAInt") [sortAInt, sortAInt] sortABool

applyLeqAInt
    :: CommonStepPattern Object
    -> CommonStepPattern Object
    -> CommonStepPattern Object
applyLeqAInt child1 child2 = applySymbol_ symbolLeqAInt [child1, child2]

varI1, varI2, varKRemainder, varStateCell :: CommonStepPattern Object

varI1 =
    mkVar Variable
        { variableName = testId "VarI1"
        , variableSort = sortAInt
        }

varI2 =
    mkVar Variable
        { variableName = testId "VarI2"
        , variableSort = sortAInt
        }

varKRemainder =
    mkVar Variable
        { variableName = testId "VarDotVar1"
        , variableSort = sortK
        }

varStateCell =
    mkVar Variable
        { variableName = testId "VarDotVar0"
        , variableSort = sortStateCell
        }

parseAxiom :: String -> Either (Error a) KoreSentence
parseAxiom str =
    case parseOnly (koreSentenceParser <* endOfInput) "<test-string>" str of
        Left err  -> koreFail err
        Right sen -> return sen

extractIndexedModule
    :: Text
    -> Either
        (Error a)
        (Map.Map ModuleName (VerifiedModule Attribute.Null Attribute.Null))
    -> VerifiedModule Attribute.Null Attribute.Null
extractIndexedModule name eModules =
    case eModules of
        Left err -> error (printError err)
        Right modules -> fromMaybe
            (error ("Module " ++ Text.unpack name ++ " not found."))
            (Map.lookup (ModuleName name) modules)
