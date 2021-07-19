module Test.Kore.Rewrite.Rule (
    test_axiomPatterns,
    test_patternToAxiomPatternAndBack,
    test_rewritePatternToRewriteRuleAndBack,
) where

import Control.DeepSeq (
    force,
 )
import Control.Exception (
    evaluate,
 )
import Data.Default
import qualified Data.Map.Strict as Map
import Data.Text (
    Text,
 )
import qualified Data.Text as Text
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin as Builtin
import Kore.Error
import Kore.IndexedModule.IndexedModule
import Kore.Internal.ApplicationSorts (
    ApplicationSorts (..),
 )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
import Kore.Rewrite.Rule
import Kore.Rewrite.RulePattern
import Kore.Syntax.Definition hiding (
    Alias (..),
 )
import Kore.Validate.DefinitionVerifier
import qualified Kore.Verified as Verified
import Prelude.Kore
import Test.Kore (
    testId,
 )
import Test.Kore.Builtin.External
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Kore.Validate.DefinitionVerifier
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_axiomPatterns :: [TestTree]
test_axiomPatterns =
    [ axiomPatternsUnitTests
    , axiomPatternsIntegrationTests
    ]

axiomPatternsUnitTests :: TestTree
axiomPatternsUnitTests =
    testGroup
        "Rule Unit Tests"
        [ testCase
            "I1:AInt => I2:AInt"
            ( assertEqual
                ""
                ( RewriteRule
                    RulePattern
                        { left = varI1
                        , antiLeft = Nothing
                        , requires = Predicate.makeTruePredicate
                        , rhs =
                            RHS
                                { existentials = []
                                , right = varI2
                                , ensures = Predicate.makeTruePredicate
                                }
                        , attributes = def
                        }
                )
                ( simpleRewriteTermToRule
                    def
                    (mkRewriteAxiomPattern varI1 varI2 Nothing)
                )
            )
        , testCase
            "alias as rule LHS"
            ( assertEqual
                ""
                ( RewriteRule
                    RulePattern
                        { left = varI1
                        , antiLeft = Nothing
                        , requires = Predicate.makeTruePredicate
                        , rhs =
                            RHS
                                { existentials = []
                                , right = varI2
                                , ensures = Predicate.makeTruePredicate
                                }
                        , attributes = def
                        }
                )
                ( simpleRewriteTermToRule
                    def
                    (mkAliasAxiomPattern applyAliasLHS varI2)
                )
            )
        , let axiom1, axiom2 :: Verified.Sentence
              axiom1 = mkRewriteAxiom varI1 varI2 Nothing
              axiom2 =
                (SentenceAxiomSentence . mkAxiom_)
                    ( applyInj
                        sortKItem
                        ( mkRewrites
                            (mkAnd mkTop_ varI1)
                            (mkAnd mkTop_ varI2)
                        )
                    )
              moduleTest =
                Module
                    { moduleName = ModuleName "TEST"
                    , moduleSentences =
                        (fmap . fmap)
                            externalize
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
                        , definitionModules = [moduleTest]
                        }
           in testCase "definition containing I1:AInt => I2:AInt"
              --TODO(traiansf): such checks should be made during verification
              $
                assertErrorIO
                    (assertSubstring "" "Unsupported pattern type in axiom")
                    ( evaluate . force
                        . map fromSentenceAxiom
                        . indexedModuleAxioms
                        $ extractIndexedModule "TEST" indexedDefinition
                    )
        , testCase "(I1:AInt => I2:AInt)::KItem" $
            assertErrorIO
                (assertSubstring "" "Unsupported pattern type in axiom")
                ( evaluate $
                    force
                        ( fromSentenceAxiom
                            ( def
                            , mkAxiom_
                                ( applySymbol
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
        [ testCase
            "I1 <= I2 => I1 <=Int I2 (generated)"
            ( assertEqual
                ""
                (RewriteRule rule)
                ( simpleRewriteTermToRule
                    def
                    (mkRewriteAxiomPattern left right Nothing)
                )
            )
        ]
  where
    left =
        applyTCell
            ( applyKCell
                ( applyKSeq
                    ( applyInj
                        sortKItem
                        ( applyLeqAExp
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
            ( applyKCell
                ( applyKSeq
                    ( applyInj
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
            , requires = Predicate.makeTruePredicate
            , rhs =
                RHS
                    { existentials = []
                    , right
                    , ensures = Predicate.makeTruePredicate
                    }
            , attributes = def
            }

test_rewritePatternToRewriteRuleAndBack :: TestTree
test_rewritePatternToRewriteRuleAndBack =
    testGroup
        "rewrite pattern to rewrite rule to pattern"
        [ let leftPSort = termLikeSort leftP
              initialLhs =
                mkAnd
                    (Predicate.fromPredicate leftPSort requiresP)
                    leftP
              initialPattern =
                Rewrites Mock.testSort initialLhs initialRhs
              finalTerm = mkRewrites initialLhs initialRhs
           in testCase "RewriteRule without antileft" $
                assertEqual
                    ""
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
        [ let op = aPG $ termLikeSort leftP
              initialPattern =
                mkImplies
                    leftP
                    (mkApplyAlias op [mkElemVar Mock.x])
           in testCase "implication axioms:" $
                assertEqual
                    ""
                    (Right initialPattern)
                    (perhapsFinalPattern def initialPattern)
        ]
  where
    perhapsFinalPattern attribute initialPattern =
        axiomPatternToTerm
            <$> termToAxiomPattern attribute initialPattern

leftP, rightP, initialRhs :: TermLike VariableName
leftP = mkElemVar Mock.x
rightP = mkExists Mock.y (mkElemVar Mock.y)
initialRhs = mkAnd (Predicate.fromPredicate sort ensuresP) rightP
  where
    sort = termLikeSort rightP

requiresP, ensuresP :: Predicate.Predicate VariableName
requiresP = Predicate.makeCeilPredicate (mkElemVar Mock.z)
ensuresP = Predicate.makeCeilPredicate (mkElemVar Mock.t)

varI1, varI2, varKRemainder, varStateCell :: TermLike VariableName
varI1 = mkElemVar $ mkElementVariable (testId "VarI1") sortAInt
varI2 = mkElemVar $ mkElementVariable (testId "VarI2") sortAInt
varKRemainder = mkElemVar $ mkElementVariable (testId "VarDotVar1") sortK
varStateCell = mkElemVar $ mkElementVariable (testId "VarDotVar0") sortStateCell

sortABool, sortAInt, sortAExp, sortBExp :: Sort
sortABool = simpleSort (SortName "ABool")
sortAInt = simpleSort (SortName "AInt")
sortAExp = simpleSort (SortName "AExp")
sortBExp = simpleSort (SortName "BExp")

applyAliasLHS :: TermLike VariableName
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

applyInj ::
    -- | destination sort
    Sort ->
    -- | argument
    TermLike VariableName ->
    TermLike VariableName
applyInj sortTo child =
    applySymbol symbolInj [sortFrom, sortTo] [child]
  where
    TermAttributes{termSort = sortFrom} = extractAttributes child

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
    sentence :: SentenceSort
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
    sentence :: SentenceSort
    sentence =
        SentenceSort
            { sentenceSortName = testId "KItem"
            , sentenceSortParameters = []
            , sentenceSortAttributes = Attributes []
            }

symbolSentenceInj :: Sentence (TermLike VariableName)
symbolSentenceInj = asSentence symbolInj

extractIndexedModule ::
    Text ->
    Either
        (Error a)
        (Map.Map ModuleName (VerifiedModule Attribute.Symbol)) ->
    VerifiedModule Attribute.Symbol
extractIndexedModule name eModules =
    case eModules of
        Left err -> error (printError err)
        Right modules ->
            fromMaybe
                (error ("Module " ++ Text.unpack name ++ " not found."))
                (Map.lookup (ModuleName name) modules)

symbolLeqAInt :: SentenceSymbol
symbolLeqAInt = mkSymbol_ (testId "leqAInt") [sortAInt, sortAInt] sortABool

applyLeqAInt ::
    TermLike VariableName ->
    TermLike VariableName ->
    TermLike VariableName
applyLeqAInt child1 child2 = applySymbol_ symbolLeqAInt [child1, child2]

symbolLeqAExp :: SentenceSymbol
symbolLeqAExp = mkSymbol_ (testId "leqAExp") [sortAExp, sortAExp] sortBExp

applyLeqAExp ::
    TermLike VariableName ->
    TermLike VariableName ->
    TermLike VariableName
applyLeqAExp child1 child2 =
    applySymbol_ symbolLeqAExp [child1, child2]

symbolKSeq, symbolInj :: SentenceSymbol
symbolKSeq = mkSymbol_ (testId "kseq") [sortKItem, sortK] sortK
symbolInj =
    mkSymbol
        (testId "inj")
        [sortParam "From", sortParam "To"]
        [sortParamSort "From"]
        (sortParamSort "To")

symbolTCell, symbolKCell :: SentenceSymbol
symbolTCell = mkSymbol_ (testId "T") [sortKCell, sortStateCell] sortTCell

-- symbol T{}(KCell{}, StateCell{}) : TCell{} []
applyTCell ::
    -- | K cell
    TermLike VariableName ->
    -- | State cell
    TermLike VariableName ->
    TermLike VariableName
applyTCell kCell stateCell =
    applySymbol_ symbolTCell [kCell, stateCell]

symbolKCell = mkSymbol_ (testId "k") [sortK] sortKCell
applyKCell ::
    TermLike VariableName ->
    TermLike VariableName
applyKCell child = applySymbol_ symbolKCell [child]

applyKSeq ::
    -- | head
    TermLike VariableName ->
    -- | tail
    TermLike VariableName ->
    TermLike VariableName
applyKSeq kHead kTail =
    applySymbol_ symbolKSeq [kHead, kTail]

sortParam :: Text -> SortVariable
sortParam name = SortVariable (testId name)

sortParamSort :: Text -> Sort
sortParamSort = SortVariableSort . sortParam

mkRewriteAxiomPattern ::
    -- | left-hand side
    TermLike VariableName ->
    -- | right-hand side
    TermLike VariableName ->
    -- | requires clause
    Maybe (Sort -> TermLike VariableName) ->
    Rewrites Sort (TermLike VariableName)
mkRewriteAxiomPattern lhs rhs requires =
    Rewrites
        patternSort
        (mkAnd (fromMaybe mkTop requires patternSort) lhs)
        (mkAnd (mkTop patternSort) rhs)
  where
    patternSort = termLikeSort lhs

mkAliasAxiomPattern ::
    -- | left-hand side
    TermLike VariableName ->
    -- | right-hand side
    TermLike VariableName ->
    Rewrites Sort (TermLike VariableName)
mkAliasAxiomPattern aliasLhs rhs =
    Rewrites
        patternSort
        aliasLhs
        (mkAnd (mkTop patternSort) rhs)
  where
    patternSort = termLikeSort aliasLhs
