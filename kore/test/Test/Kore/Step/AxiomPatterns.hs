module Test.Kore.Step.AxiomPatterns
    ( test_axiomPatterns
    , test_freeVariables
    , test_refreshRulePattern
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import           Data.Default
import qualified Data.Foldable as Foldable
import qualified Data.Map as Map
import           Data.Maybe
                 ( fromMaybe )
import           Data.Proxy
                 ( Proxy (..) )
import qualified Data.Set as Set
import           Data.Text
                 ( Text )
import qualified Data.Text as Text

import           Kore.AST.Builders
import           Kore.AST.Kore
import           Kore.AST.Pure
import           Kore.AST.Sentence
import           Kore.AST.Valid as Valid
import           Kore.ASTVerifier.DefinitionVerifier
                 ( AttributesVerification (..), verifyAndIndexDefinition )
import qualified Kore.Attribute.Null as Attribute
import qualified Kore.Builtin as Builtin
import           Kore.Error
import           Kore.IndexedModule.IndexedModule
                 ( VerifiedModule )
import           Kore.Parser.ParserImpl
import           Kore.Parser.ParserUtils
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.AxiomPatterns hiding
                 ( freeVariables )
import qualified Kore.Step.AxiomPatterns as AxiomPatterns
import           Kore.Step.Pattern

import           Test.Kore
                 ( testId )
import           Test.Kore.ASTVerifier.DefinitionVerifier
import qualified Test.Kore.Step.MockSymbols as Mock

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
                    , requires = Predicate.wrapPredicate (mkTop sortAInt)
                    , ensures = Predicate.wrapPredicate (mkTop sortAInt)
                    , attributes = def
                    }
                )
                (koreSentenceToAxiomPattern Object
                    (mkRewriteAxiom varI1 varI2 Nothing)
                )
            )
        ,   let
                axiom1 :: VerifiedKoreSentence
                axiom1 = mkRewriteAxiom varI1 varI2 Nothing
                axiom2 :: VerifiedKoreSentence
                axiom2 =
                    (asKoreAxiomSentence . toKoreSentenceAxiom . mkAxiom_)
                        (applyInj sortKItem
                            (mkRewrites
                                (mkAnd mkTop_ varI1)
                                (mkAnd mkTop_ varI2)
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
                                , toKoreSentence symbolSentenceInj
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
                        , requires = Predicate.wrapPredicate (mkTop sortAInt)
                        , ensures = Predicate.wrapPredicate (mkTop sortAInt)
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
                    ((asKoreAxiomSentence . toKoreSentenceAxiom . mkAxiom_)
                        (applySymbol
                            symbolInj
                            [sortAInt, sortKItem]
                            [ mkRewrites
                                (mkAnd mkTop_ varI1)
                                (mkAnd mkTop_ varI2)
                            ]
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
                    , requires = Predicate.wrapPredicate (mkTop sortTCell)
                    , ensures = Predicate.wrapPredicate (mkTop sortTCell)
                    , attributes = def
                    }
                )
                (do
                    parsed <-
                        parseAxiom
                            "axiom{}\n\
                            \    \\rewrites{TCell{}}(\n\
                            \        \\and{TCell{}}(\n\
                            \            \\top{TCell{}}(),\n\
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
                            \            )\n\
                            \        ),\n\
                            \        \\and{TCell{}}(\n\
                            \            \\top{TCell{}}(),\n\
                            \            T{}(\n\
                            \                k{}(\n\
                            \                    kseq{}(\n\
                            \                       inj{ABool{}, KItem{}}(\n\
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
                            \[]"
                    let valid =
                            UnifiedObject Valid { patternSort, freeVariables }
                          where
                            patternSort = sortTCell
                            freeVariables =
                                Set.fromList
                                    [ asUnified (Variable "VarI1" mempty sortAInt)
                                    , asUnified (Variable "VarI2" mempty sortAInt)
                                    , asUnified (Variable "VarDotVar1" mempty sortK)
                                    , asUnified (Variable "VarDotVar0" mempty sortStateCell)
                                    ]
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
    toKoreSentence (asSentence sentence)
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
    toKoreSentence (asSentence sentence)
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
        , variableCounter = mempty
        , variableSort = sortAInt
        }

varI2 =
    mkVar Variable
        { variableName = testId "VarI2"
        , variableCounter = mempty
        , variableSort = sortAInt
        }

varKRemainder =
    mkVar Variable
        { variableName = testId "VarDotVar1"
        , variableCounter = mempty
        , variableSort = sortK
        }

varStateCell =
    mkVar Variable
        { variableName = testId "VarDotVar0"
        , variableCounter = mempty
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

test_freeVariables :: TestTree
test_freeVariables =
    testCase "Extract free variables" $ do
        let expect = Set.fromList [Mock.x, Mock.z]
            actual = AxiomPatterns.freeVariables testRulePattern
        assertEqual "Expected free variables" expect actual

test_refreshRulePattern :: TestTree
test_refreshRulePattern =
    testCase "Rename target variables" $ do
        let avoiding = AxiomPatterns.freeVariables testRulePattern
            (renaming, rulePattern') =
                refreshRulePattern avoiding testRulePattern
            renamed = Set.fromList (Foldable.toList renaming)
            free' = AxiomPatterns.freeVariables rulePattern'
        assertEqual
            "Expected to rename all free variables of original RulePattern"
            avoiding
            (Map.keysSet renaming)
        assertBool
            "Expected to renamed variables distinct from original variables"
            (Set.null $ Set.intersection avoiding renamed)
        assertBool
            "Expected no free variables in common with original RulePattern"
            (Set.null $ Set.intersection avoiding free')

testRulePattern :: RulePattern Object Variable
testRulePattern =
    RulePattern
        { left =
            -- Include an implicitly-quantified variable.
            mkVar Mock.x
        , right =
            -- Include a binder to ensure that we respect them.
            mkExists Mock.y (mkVar Mock.y)
        , requires = Predicate.makeCeilPredicate (mkVar Mock.z)
        , ensures = Predicate.makeTruePredicate
        , attributes = def
        }
