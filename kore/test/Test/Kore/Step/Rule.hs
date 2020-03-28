module Test.Kore.Step.Rule
    ( test_axiomPatterns
    , test_patternToAxiomPatternAndBack
    , test_rewritePatternToRewriteRuleAndBack
    ) where

import Prelude.Kore

import Test.Tasty
import Test.Tasty.HUnit.Ext

import Control.DeepSeq
    ( force
    )
import Control.Exception
    ( evaluate
    )
import Data.Default
import Data.Generics.Product
import qualified Data.Map.Strict as Map
import Data.Text
    ( Text
    )
import qualified Data.Text as Text

import Kore.ASTVerifier.DefinitionVerifier
import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Pattern as Attribute
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin as Builtin
import Kore.Error
import Kore.IndexedModule.IndexedModule
import Kore.Internal.ApplicationSorts
    ( ApplicationSorts (..)
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
import Kore.Step.Rule
import Kore.Step.RulePattern
import Kore.Syntax.Definition hiding
    ( Alias (..)
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
                (RewriteRule RulePattern
                    { left = varI1
                    , antiLeft = Nothing
                    , requires = Predicate.makeTruePredicate sortAInt
                    , rhs = RHS
                        { existentials = []
                        , right = varI2
                        , ensures = Predicate.makeTruePredicate sortAInt
                        }
                    , attributes = def
                    }
                )
                (simpleRewriteTermToRule def
                    (mkRewriteAxiomPattern varI1 varI2 Nothing)
                )
            )
        , testCase "alias as rule LHS"
            (assertEqual ""
                ( RewriteRule RulePattern
                    { left = varI1
                    , antiLeft = Nothing
                    , requires = Predicate.makeTruePredicate sortAInt
                    , rhs = RHS
                        { existentials = []
                        , right = varI2
                        , ensures = Predicate.makeTruePredicate sortAInt
                        }
                    , attributes = def
                    }
                )
                (simpleRewriteTermToRule def
                    (mkAliasAxiomPattern applyAliasLHS varI2)
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
                        Builtin.koreVerifiers
                        Definition
                            { definitionAttributes = Attributes []
                            , definitionModules = [ moduleTest ]
                            }
            in
                testCase "definition containing I1:AInt => I2:AInt"
                --TODO(traiansf): such checks should be made during verification
                $ assertErrorIO
                    (assertSubstring "" "Unsupported pattern type in axiom")
                    (evaluate . force
                    . map fromSentenceAxiom . indexedModuleAxioms
                    $ extractIndexedModule "TEST" indexedDefinition
                    )
        , testCase "(I1:AInt => I2:AInt)::KItem"
            $ assertErrorIO
                (assertSubstring "" "Unsupported pattern type in axiom")
                (evaluate $ force
                    (fromSentenceAxiom
                        ( def
                        , mkAxiom_
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
                (RewriteRule rule)
                (simpleRewriteTermToRule def
                    (mkRewriteAxiomPattern left right Nothing)
                )
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
            , requires = Predicate.makeTruePredicate sortTCell
            , rhs = RHS
                { existentials = []
                , right
                , ensures = Predicate.makeTruePredicate sortTCell
                }
            , attributes = def
            }

test_rewritePatternToRewriteRuleAndBack :: TestTree
test_rewritePatternToRewriteRuleAndBack =
    testGroup
        "rewrite pattern to rewrite rule to pattern"
        [
            let initialLhs =
                    mkAnd
                        (mkNot antiLeftP)
                        (mkAnd (Predicate.unwrapPredicate requiresP) leftP)
                initialPattern =
                    Rewrites Mock.testSort initialLhs initialRhs
                finalTerm = mkRewrites initialLhs initialRhs
            in
                testCase "RewriteRule with antileft" $
                    assertEqual ""
                        finalTerm
                        (perhapsFinalPattern
                            attributesWithPriority
                            initialPattern
                        )
        ,
            let initialLhs = mkAnd (Predicate.unwrapPredicate requiresP) leftP
                initialPattern =
                    Rewrites Mock.testSort initialLhs initialRhs
                finalTerm = mkRewrites initialLhs initialRhs
            in
                testCase "RewriteRule without antileft" $
                    assertEqual ""
                        finalTerm
                        (perhapsFinalPattern def initialPattern)
        ]
  where
    perhapsFinalPattern attribute initialPattern =
        rewriteRuleToTerm $ simpleRewriteTermToRule attribute initialPattern

test_patternToAxiomPatternAndBack :: TestTree
test_patternToAxiomPatternAndBack =
    testGroup
        "pattern to axiomPattern to pattern"
        [
             let op = wEF $ termLikeSort leftP
                 initialPattern = mkImplies
                    (mkAnd (Predicate.unwrapPredicate requiresP) leftP)
                    (mkApplyAlias
                        op
                        [mkAnd (Predicate.unwrapPredicate ensuresP) rightP]
                    )
            in
                testCase "Reachability claim wEF" $
                    assertEqual ""
                        (Right initialPattern)
                        (perhapsFinalPattern def initialPattern)
        ,
            let op = wAF $ termLikeSort leftP
                initialPattern = mkImplies
                    (mkAnd (Predicate.unwrapPredicate requiresP) leftP)
                    (mkApplyAlias
                        op
                        [mkAnd (Predicate.unwrapPredicate ensuresP) rightP]
                    )
            in
                testCase "Reachability claim wAF" $
                    assertEqual ""
                        (Right initialPattern)
                        (perhapsFinalPattern def initialPattern)
        ,
            let initialPattern = mkImplies
                    (Predicate.unwrapPredicate requiresP)
                    (mkAnd (mkEquals_ leftP rightP) mkTop_)
            in
                testCase "Function axioms: general" $
                    assertEqual ""
                        (Right initialPattern)
                        (perhapsFinalPattern def initialPattern)
        ,
            let initialPattern = mkEquals_ leftP rightP
            in
                testCase "Function axioms: trivial pre- and post-conditions" $
                    assertEqual ""
                        (Right initialPattern)
                        (perhapsFinalPattern def initialPattern)
        ,
            let initialPattern = mkCeil (termLikeSort (mkElemVar Mock.x))
                                    $ mkElemVar Mock.x
            in
                testCase "Definedness axioms" $
                    assertEqual ""
                        (Right initialPattern)
                        (perhapsFinalPattern def initialPattern)
        ,
            let op = aPG $ termLikeSort leftP
                initialPattern = mkImplies
                    leftP
                    (mkApplyAlias op [mkElemVar Mock.x])
            in
                testCase "implication axioms:" $
                    assertEqual ""
                        (Right initialPattern)
                        (perhapsFinalPattern def initialPattern)
        ]
  where
    perhapsFinalPattern attribute initialPattern = axiomPatternToTerm
        <$> termToAxiomPattern attribute initialPattern

leftP, antiLeftP, rightP, initialRhs :: TermLike Variable
leftP = mkElemVar Mock.x
antiLeftP = mkElemVar Mock.u
rightP = mkExists Mock.y (mkElemVar Mock.y)
initialRhs = mkAnd (Predicate.unwrapPredicate ensuresP) rightP

requiresP, ensuresP :: Predicate.Predicate Variable
requiresP = Predicate.makeCeilPredicate_ (mkElemVar Mock.z)
ensuresP = Predicate.makeCeilPredicate_ (mkElemVar Mock.t)

attributesWithPriority :: Ord variable => Attribute.Axiom symbol variable
attributesWithPriority =
    def & setField @"priority" (Attribute.Priority (Just 0))

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

sortABool, sortAInt, sortAExp, sortBExp :: Sort
sortABool = simpleSort (SortName "ABool")
sortAInt = simpleSort (SortName "AInt")
sortAExp = simpleSort (SortName "AExp")
sortBExp = simpleSort (SortName "BExp")

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


applyInj
    :: Sort  -- ^ destination sort
    -> TermLike Variable  -- ^ argument
    -> TermLike Variable
applyInj sortTo child =
    applySymbol symbolInj [sortFrom, sortTo] [child]
  where
    Attribute.Pattern { patternSort = sortFrom } = extractAttributes child

sortK, sortKItem, sortKCell, sortStateCell, sortTCell :: Sort
sortK = simpleSort (SortName "K")
sortKItem = simpleSort (SortName "KItem")

sortKCell = simpleSort (SortName "KCell")
sortStateCell = simpleSort (SortName "StateCell")
sortTCell = simpleSort (SortName "TCell")


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

symbolSentenceInj :: Sentence (TermLike Variable)
symbolSentenceInj = asSentence symbolInj

extractIndexedModule
    :: Text
    -> Either
        (Error a)
        (Map.Map ModuleName (VerifiedModule Attribute.Symbol))
    -> VerifiedModule Attribute.Symbol
extractIndexedModule name eModules =
    case eModules of
        Left err -> error (printError err)
        Right modules -> fromMaybe
            (error ("Module " ++ Text.unpack name ++ " not found."))
            (Map.lookup (ModuleName name) modules)

symbolLeqAInt :: SentenceSymbol (TermLike Variable)
symbolLeqAInt = mkSymbol_ (testId "leqAInt") [sortAInt, sortAInt] sortABool

applyLeqAInt
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
applyLeqAInt child1 child2 = applySymbol_ symbolLeqAInt [child1, child2]

symbolLeqAExp :: SentenceSymbol (TermLike Variable)
symbolLeqAExp = mkSymbol_ (testId "leqAExp") [sortAExp, sortAExp] sortBExp

applyLeqAExp
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
applyLeqAExp child1 child2 =
    applySymbol_ symbolLeqAExp [child1, child2]

symbolKSeq, symbolInj :: SentenceSymbol (TermLike Variable)
symbolKSeq = mkSymbol_ (testId "kseq") [sortKItem, sortK] sortK

symbolInj =
    mkSymbol
        (testId "inj")
        [sortParam "From", sortParam "To"]
        [sortParamSort "From"]
        (sortParamSort "To")

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

applyKSeq
    :: TermLike Variable  -- ^ head
    -> TermLike Variable  -- ^ tail
    -> TermLike Variable
applyKSeq kHead kTail =
    applySymbol_ symbolKSeq [kHead, kTail]

sortParam :: Text -> SortVariable
sortParam name = SortVariable (testId name)

sortParamSort :: Text -> Sort
sortParamSort = SortVariableSort . sortParam

mkRewriteAxiomPattern
    :: TermLike Variable  -- ^ left-hand side
    -> TermLike Variable  -- ^ right-hand side
    -> Maybe (Sort -> TermLike Variable)  -- ^ requires clause
    -> Rewrites Sort (TermLike Variable)
mkRewriteAxiomPattern lhs rhs requires =
    Rewrites
        patternSort
        (mkAnd (fromMaybe mkTop requires patternSort) lhs)
        (mkAnd (mkTop patternSort) rhs)
  where
    patternSort = termLikeSort lhs

mkAliasAxiomPattern
    :: TermLike Variable  -- ^ left-hand side
    -> TermLike Variable  -- ^ right-hand side
    -> Rewrites Sort (TermLike Variable)
mkAliasAxiomPattern aliasLhs rhs =
    Rewrites
        patternSort
        aliasLhs
        (mkAnd (mkTop patternSort) rhs)
  where
    patternSort = termLikeSort aliasLhs
