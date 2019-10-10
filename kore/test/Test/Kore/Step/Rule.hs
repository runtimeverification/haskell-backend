module Test.Kore.Step.Rule
    ( test_axiomPatterns
    , test_freeVariables
    , test_refreshRulePattern
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import Data.Default
import qualified Data.Foldable as Foldable
import qualified Data.Map as Map
import Data.Maybe
    ( fromMaybe
    )
import qualified Data.Set as Set
import Data.Text
    ( Text
    )
import qualified Data.Text as Text

import Kore.ASTVerifier.DefinitionVerifier
import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Pattern as Attribute
import Kore.Attribute.Pattern.FreeVariables as FreeVariables
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin as Builtin
import Kore.Error
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    )
import Kore.Internal.ApplicationSorts
    ( ApplicationSorts (..)
    )
import Kore.Internal.TermLike hiding
    ( freeVariables
    )
import qualified Kore.Predicate.Predicate as Predicate
import Kore.Step.Rule hiding
    ( freeVariables
    )
import qualified Kore.Step.Rule as Rule
import Kore.Syntax.Definition hiding
    ( Alias (..)
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )
import qualified Kore.Verified as Verified

import Test.Kore
    ( testId
    )
import Test.Kore.ASTVerifier.DefinitionVerifier
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
                    , antiLeft = Nothing
                    , right = varI2
                    , requires = Predicate.wrapPredicate (mkTop sortAInt)
                    , ensures = Predicate.wrapPredicate (mkTop sortAInt)
                    , attributes = def
                    }
                )
                (Rule.fromSentence $ mkRewriteAxiom varI1 varI2 Nothing)
            )
        , testCase "alias as rule LHS"
            (assertEqual ""
                ( Right $ RewriteAxiomPattern $ RewriteRule RulePattern
                    { left = varI1
                    , antiLeft = Nothing
                    , right = varI2
                    , requires = Predicate.wrapPredicate (mkTop sortAInt)
                    , ensures = Predicate.wrapPredicate (mkTop sortAInt)
                    , attributes = def
                    }
                )
                (Rule.fromSentence . SentenceAxiomSentence . mkAxiom_ $
                    mkRewrites
                        applyAliasLHS
                        (mkAnd (mkTop sortAInt) varI2)
                )
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
                            (fmap . fmap) Builtin.externalize
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
                        , antiLeft = Nothing
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
                (Right $ FunctionAxiomPattern $ EqualityRule $ rulePattern
                    (mkCeil sortR term)
                    (mkTop sortR)
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
                (Right $ RewriteAxiomPattern $ RewriteRule rule)
                (Rule.fromSentence $ Rule.mkRewriteAxiom left right Nothing)
            )
        ]
  where
    left =
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
    right =
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
    rule =
        RulePattern
            { left
            , antiLeft = Nothing
            , right
            , requires = Predicate.wrapPredicate (mkTop sortTCell)
            , ensures = Predicate.wrapPredicate (mkTop sortTCell)
            , attributes = def
            }

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
    asSentence sentence
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
    asSentence sentence
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
    Attribute.Pattern { patternSort = sortFrom } = extractAttributes child

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
    mkElemVar $ ElementVariable Variable
        { variableName = testId "VarI1"
        , variableCounter = mempty
        , variableSort = sortAInt
        }

varI2 =
    mkElemVar $ ElementVariable Variable
        { variableName = testId "VarI2"
        , variableCounter = mempty
        , variableSort = sortAInt
        }

varKRemainder =
    mkElemVar $ ElementVariable Variable
        { variableName = testId "VarDotVar1"
        , variableCounter = mempty
        , variableSort = sortK
        }

varStateCell =
    mkElemVar $ ElementVariable Variable
        { variableName = testId "VarDotVar0"
        , variableCounter = mempty
        , variableSort = sortStateCell
        }

applyAliasLHS :: TermLike Variable
applyAliasLHS =
    mkApplyAlias ruleLHS []
  where
    ruleLHS =
        Alias
            { aliasConstructor = testId "RuleLHS"
            , aliasParams = []
            , aliasSorts =
                ApplicationSorts
                    { applicationSortsOperands = []
                    , applicationSortsResult = sortAInt
                    }
            , aliasLeft = []
            , aliasRight =
                mkAnd (mkTop sortAInt) varI1
            }


extractIndexedModule
    :: Text
    -> Either
        (Error a)
        (Map.Map ModuleName (VerifiedModule Attribute.Symbol Attribute.Axiom))
    -> VerifiedModule Attribute.Symbol Attribute.Axiom
extractIndexedModule name eModules =
    case eModules of
        Left err -> error (printError err)
        Right modules -> fromMaybe
            (error ("Module " ++ Text.unpack name ++ " not found."))
            (Map.lookup (ModuleName name) modules)

test_freeVariables :: TestTree
test_freeVariables =
    testCase "Extract free variables" $ do
        let expect =
                FreeVariables . Set.fromList
                $ ElemVar <$> [Mock.x, Mock.z, Mock.t, Mock.u]
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
            notAvoided x = not (FreeVariables.isFreeVariable x avoiding)
        assertEqual
            "Expected to rename all free variables of original RulePattern"
            (getFreeVariables avoiding)
            (Map.keysSet renaming)
        assertBool
            "Expected to renamed variables distinct from original variables"
            (all notAvoided renamed)
        assertBool
            "Expected no free variables in common with original RulePattern"
            (all notAvoided (FreeVariables.getFreeVariables free'))

testRulePattern :: RulePattern Variable
testRulePattern =
    RulePattern
        { left =
            -- Include an implicitly-quantified variable.
            mkElemVar Mock.x
        , antiLeft = Just $ mkElemVar Mock.u
        , right =
            -- Include a binder to ensure that we respect them.
            mkExists Mock.y (mkElemVar Mock.y)
        , requires = Predicate.makeCeilPredicate (mkElemVar Mock.z)
        , ensures = Predicate.makeCeilPredicate (mkElemVar Mock.t)
        , attributes = def
        }
