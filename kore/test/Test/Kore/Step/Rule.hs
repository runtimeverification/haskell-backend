module Test.Kore.Step.Rule
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
import qualified Data.Set as Set
import           Data.Text
                 ( Text )
import qualified Data.Text as Text

import           Kore.ASTVerifier.DefinitionVerifier
import qualified Kore.Attribute.Null as Attribute
import qualified Kore.Attribute.Pattern as Attribute
import qualified Kore.Builtin as Builtin
import           Kore.Error
import           Kore.IndexedModule.IndexedModule
                 ( VerifiedModule )
import           Kore.Internal.TermLike hiding
                 ( freeVariables )
import           Kore.Parser.Parser
import           Kore.Parser.ParserUtils
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Rule hiding
                 ( freeVariables )
import qualified Kore.Step.Rule as Rule
import           Kore.Syntax.Definition
import qualified Kore.Verified as Verified

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
        "Rule Unit Tests"
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
                (Rule.fromSentence $ mkRewriteAxiom varI1 varI2 Nothing)
            )
        ,   let
                axiom1, axiom2 :: Verified.Sentence
                axiom1 = mkRewriteAxiom varI1 varI2 Nothing
                axiom2 =
                    (SentenceAxiomSentence . mkAxiom_)
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
                                eraseSentenceAnnotations
                                [ axiom1
                                , axiom2
                                , sortSentenceAInt
                                , sortSentenceKItem
                                , symbolSentenceInj
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
                    (extractRewriteAxioms
                        (extractIndexedModule "TEST" indexedDefinition)
                    )
        , testCase "\\ceil(I1:AInt <= I2:AInt)" $ do
            let term = applyLeqAInt varI1 varI2
                sortR = mkSortVariable (testId "R")
            assertEqual ""
                (Right $ FunctionAxiomPattern $ EqualityRule RulePattern
                    { left = mkCeil sortR term
                    , right = mkTop sortR
                    , requires = Predicate.makeTruePredicate
                    , ensures = Predicate.makeTruePredicate
                    , attributes = def
                    }
                )
                (Rule.fromSentence $ mkCeilAxiom term)
        , testCase "(I1:AInt => I2:AInt)::KItem"
            (assertEqual ""
                (koreFail "Unsupported pattern type in axiom")
                (Rule.fromSentenceAxiom
                    (mkAxiom_
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
        "Rule Unit Tests"
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
                            Attribute.Pattern
                                { patternSort = sortTCell
                                , freeVariables =
                                    Set.fromList
                                        [ varS "VarI1" sortAInt
                                        , varS "VarI2" sortAInt
                                        , varS "VarDotVar1" sortK
                                        , varS "VarDotVar0" sortStateCell
                                        ]
                                }
                    Rule.fromSentence ((<$) valid <$> parsed)
                )
            )
        ]

sortK, sortKItem, sortKCell, sortStateCell, sortTCell :: Sort
sortK = simpleSort (SortName "K")
sortKItem = simpleSort (SortName "KItem")

sortKCell = simpleSort (SortName "KCell")
sortStateCell = simpleSort (SortName "StateCell")
sortTCell = simpleSort (SortName "TCell")

sortABool, sortAInt, sortAExp, sortBExp :: Sort
sortABool = simpleSort (SortName "ABool")
sortAInt = simpleSort (SortName "AInt")
sortAExp = simpleSort (SortName "AExp")
sortBExp = simpleSort (SortName "BExp")

sortSentenceAInt :: Verified.Sentence
sortSentenceAInt =
    (asSentence sentence)
  where
    sentence :: SentenceSort (TermLike Variable)
    sentence =
        SentenceSort
            { sentenceSortName = testId "AInt"
            , sentenceSortParameters = []
            , sentenceSortAttributes = Attributes []
            }

sortSentenceKItem :: Verified.Sentence
sortSentenceKItem =
    (asSentence sentence)
  where
    sentence :: SentenceSort (TermLike Variable)
    sentence =
        SentenceSort
            { sentenceSortName = testId "KItem"
            , sentenceSortParameters = []
            , sentenceSortAttributes = Attributes []
            }

sortParam :: Text -> SortVariable
sortParam name = SortVariable (testId name)

sortParamSort :: Text -> Sort
sortParamSort = SortVariableSort . sortParam

symbolTCell, symbolKCell :: SentenceSymbol (TermLike Variable)
symbolTCell = mkSymbol_ (testId "T") [sortKCell, sortStateCell] sortTCell
-- symbol T{}(KCell{}, StateCell{}) : TCell{} []
applyTCell
    :: TermLike Variable  -- ^ K cell
    -> TermLike Variable  -- ^ State cell
    -> TermLike Variable
applyTCell kCell stateCell =
    applySymbol_ symbolTCell [kCell, stateCell]

symbolKCell = mkSymbol_ (testId "k") [sortK] sortKCell
applyKCell
    :: TermLike Variable
    -> TermLike Variable
applyKCell child = applySymbol_ symbolKCell [child]

symbolKSeq, symbolInj :: SentenceSymbol (TermLike Variable)
symbolKSeq = mkSymbol_ (testId "kseq") [sortKItem, sortK] sortK

symbolInj =
    mkSymbol
        (testId "inj")
        [sortParam "From", sortParam "To"]
        [sortParamSort "From"]
        (sortParamSort "To")

applyKSeq
    :: TermLike Variable  -- ^ head
    -> TermLike Variable  -- ^ tail
    -> TermLike Variable
applyKSeq kHead kTail =
    applySymbol_ symbolKSeq [kHead, kTail]

applyInj
    :: Sort  -- ^ destination sort
    -> TermLike Variable  -- ^ argument
    -> TermLike Variable
applyInj sortTo child =
    applySymbol symbolInj [sortFrom, sortTo] [child]
  where
    Attribute.Pattern { patternSort = sortFrom } = extract child

symbolSentenceInj :: Sentence (TermLike Variable)
symbolSentenceInj = asSentence symbolInj
-- symbol inj{From,To}(From) : To []

symbolLeqAExp :: SentenceSymbol (TermLike Variable)
symbolLeqAExp = mkSymbol_ (testId "leqAExp") [sortAExp, sortAExp] sortBExp

applyLeqAExp
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
applyLeqAExp child1 child2 =
    applySymbol_ symbolLeqAExp [child1, child2]

symbolLeqAInt :: SentenceSymbol (TermLike Variable)
symbolLeqAInt = mkSymbol_ (testId "leqAInt") [sortAInt, sortAInt] sortABool

applyLeqAInt
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
applyLeqAInt child1 child2 = applySymbol_ symbolLeqAInt [child1, child2]

varI1, varI2, varKRemainder, varStateCell :: TermLike Variable

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

parseAxiom :: String -> Either (Error a) ParsedSentence
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
            actual = Rule.freeVariables testRulePattern
        assertEqual "Expected free variables" expect actual

test_refreshRulePattern :: TestTree
test_refreshRulePattern =
    testCase "Rename target variables" $ do
        let avoiding = Rule.freeVariables testRulePattern
            (renaming, rulePattern') =
                refreshRulePattern avoiding testRulePattern
            renamed = Set.fromList (Foldable.toList renaming)
            free' = Rule.freeVariables rulePattern'
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

testRulePattern :: RulePattern Variable
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
