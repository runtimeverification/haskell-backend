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
import qualified Kore.Syntax.Sentence as Sentence
import qualified Kore.Builtin as Builtin
import Kore.Error
import Kore.IndexedModule.IndexedModule
import qualified Kore.Syntax as Syntax
import Kore.Internal.ApplicationSorts (
    ApplicationSorts (..),
    symbolOrAliasSorts,
 )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.TermLike as TermLike
import Kore.Internal.TermLike (TermLike, VariableName, Sort (..), Alias (..), TermAttributes (..), SortVariable (..), Rewrites, fromTermLike, Id, InternalVariable, termLikeSort, Rewrites(..))
import qualified Kore.Internal.Symbol as Internal
import Kore.Rewrite.Rule
import Kore.Rewrite.RulePattern
import Kore.Syntax.Definition hiding (
    Alias (..),
 )
import Kore.Validate.DefinitionVerifier
import qualified Kore.Validate as Validated
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
                    (mkRewriteAxiomPattern (fromTermLike varI1) (fromTermLike varI2) Nothing)
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
                    (mkAliasAxiomPattern applyAliasLHS (fromTermLike varI2))
                )
            )
        , let axiom1, axiom2 :: Validated.Sentence
              axiom1 =
                (SentenceAxiomSentence . mkAxiom_)
                    ( applyInjPattern
                        sortKItem
                        ( Validated.mkRewrites
                            (Validated.mkAnd (Validated.mkTop sortAInt) (fromTermLike varI1))
                            (Validated.mkAnd (Validated.mkTop sortAInt) (fromTermLike varI2))
                        )
                    )
              axiom2 =
                (SentenceAxiomSentence . mkAxiom_)
                    ( applyInjPattern
                        sortKItem
                        ( Validated.mkRewrites
                            (Validated.mkAnd (Validated.mkTop sortAInt) (fromTermLike varI1))
                            (Validated.mkAnd (Validated.mkTop sortAInt) (fromTermLike varI2))
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
                                    [ Validated.mkRewrites
                                        (Validated.mkAnd (Validated.mkTop sortAInt) (fromTermLike varI1))
                                        (Validated.mkAnd (Validated.mkTop sortAInt) (fromTermLike varI2))
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
                    (mkRewriteAxiomPattern (fromTermLike left) (fromTermLike right) Nothing)
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
        [ let leftPSort = Validated.patternSort leftP
              initialLhs =
                Validated.mkAnd
                    (Predicate.fromPredicate leftPSort requiresP)
                    leftP
              initialPattern =
                Syntax.Rewrites Mock.testSort initialLhs initialRhs
              finalTerm = Validated.mkRewrites initialLhs initialRhs
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
        [ let op = aPG $ Validated.patternSort leftP
              initialPattern =
                Validated.mkImplies
                    leftP
                    (Validated.mkApplyAlias op [Validated.mkElemVar Mock.x])
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

leftP, rightP, initialRhs :: Validated.Pattern VariableName
leftP = Validated.mkElemVar Mock.x
rightP = Validated.mkExists Mock.y (Validated.mkElemVar Mock.y)
initialRhs = Validated.mkAnd (Predicate.fromPredicate sort ensuresP) rightP
  where
    sort = Validated.patternSort rightP

requiresP, ensuresP :: Predicate.Predicate VariableName
requiresP = Predicate.makeCeilPredicate (TermLike.mkElemVar Mock.z)
ensuresP = Predicate.makeCeilPredicate (TermLike.mkElemVar Mock.t)

varI1, varI2, varKRemainder, varStateCell :: TermLike VariableName
varI1 = TermLike.mkElemVar $ Syntax.mkElementVariable (testId "VarI1") sortAInt
varI2 = TermLike.mkElemVar $ Syntax.mkElementVariable (testId "VarI2") sortAInt
varKRemainder = TermLike.mkElemVar $ Syntax.mkElementVariable (testId "VarDotVar1") sortK
varStateCell = TermLike.mkElemVar $ Syntax.mkElementVariable (testId "VarDotVar0") sortStateCell

sortABool, sortAInt, sortAExp, sortBExp :: Sort
sortABool = simpleSort (SortName "ABool")
sortAInt = simpleSort (SortName "AInt")
sortAExp = simpleSort (SortName "AExp")
sortBExp = simpleSort (SortName "BExp")

applyAliasLHS :: Validated.Pattern VariableName
applyAliasLHS =
    Validated.mkApplyAlias ruleLHS []
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
                Validated.mkAnd (Validated.mkTop sortAInt) (fromTermLike varI1)
            }

applyInj ::
    -- | destination sort
    Sort ->
    -- | argument
    TermLike VariableName ->
    TermLike VariableName
applyInj sortTo child =
    TermLike.applySymbol symbolInj [sortFrom, sortTo] [child]
  where
    TermAttributes{termSort = sortFrom} = TermLike.extractAttributes child

applyInjPattern ::
    -- | destination sort
    Sort ->
    -- | argument
    Validated.Pattern VariableName ->
    Validated.Pattern VariableName
applyInjPattern sortTo child =
    applySymbol symbolInj [sortFrom, sortTo] [child]
  where
    Validated.PatternAttributes{termSort = sortFrom} = Validated.extractAttributes child

sortK, sortKItem, sortKCell, sortStateCell, sortTCell :: Sort
sortK = simpleSort (SortName "K")
sortKItem = simpleSort (SortName "KItem")
sortKCell = simpleSort (SortName "KCell")
sortStateCell = simpleSort (SortName "StateCell")
sortTCell = simpleSort (SortName "TCell")

sortSentenceAInt :: Validated.Sentence
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

sortSentenceKItem :: Validated.Sentence
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

symbolSentenceInj :: Sentence (Validated.Pattern VariableName)
symbolSentenceInj = asSentence symbolInj

extractIndexedModule ::
    Text ->
    Either
        (Error a)
        (Map.Map ModuleName (ValidatedModule Attribute.Symbol)) ->
    ValidatedModule Attribute.Symbol
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
applyLeqAInt child1 child2 = TermLike.applySymbol_ symbolLeqAInt [child1, child2]

symbolLeqAExp :: SentenceSymbol
symbolLeqAExp = mkSymbol_ (testId "leqAExp") [sortAExp, sortAExp] sortBExp

applyLeqAExp ::
    TermLike VariableName ->
    TermLike VariableName ->
    TermLike VariableName
applyLeqAExp child1 child2 =
    TermLike.applySymbol_ symbolLeqAExp [child1, child2]

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
    TermLike.applySymbol_ symbolTCell [kCell, stateCell]

symbolKCell = mkSymbol_ (testId "k") [sortK] sortKCell
applyKCell ::
    TermLike VariableName ->
    TermLike VariableName
applyKCell child = TermLike.applySymbol_ symbolKCell [child]

applyKSeq ::
    -- | head
    TermLike VariableName ->
    -- | tail
    TermLike VariableName ->
    TermLike VariableName
applyKSeq kHead kTail =
    TermLike.applySymbol_ symbolKSeq [kHead, kTail]

sortParam :: Text -> SortVariable
sortParam name = SortVariable (testId name)

sortParamSort :: Text -> Sort
sortParamSort = SortVariableSort . sortParam

mkRewriteAxiomPattern ::
    -- | left-hand side
    Validated.Pattern VariableName ->
    -- | right-hand side
    Validated.Pattern VariableName ->
    -- | requires clause
    Maybe (Sort -> Validated.Pattern VariableName) ->
    Rewrites Sort (Validated.Pattern VariableName)
mkRewriteAxiomPattern lhs rhs requires =
    Rewrites
        patternSort
        (Validated.mkAnd (fromMaybe Validated.mkTop requires patternSort) lhs)
        (Validated.mkAnd (Validated.mkTop patternSort) rhs)
  where
    patternSort = Validated.patternSort lhs

mkAliasAxiomPattern ::
    -- | left-hand side
    Validated.Pattern VariableName ->
    -- | right-hand side
    Validated.Pattern VariableName ->
    Rewrites Sort (Validated.Pattern VariableName)
mkAliasAxiomPattern aliasLhs rhs =
    Rewrites
        patternSort
        aliasLhs
        (Validated.mkAnd (Validated.mkTop patternSort) rhs)
  where
    patternSort = Validated.patternSort aliasLhs

mkAxiom ::
    [SortVariable] ->
    Validated.Pattern variable ->
    SentenceAxiom (Validated.Pattern variable)
mkAxiom sentenceAxiomParameters sentenceAxiomPattern =
    SentenceAxiom
        { sentenceAxiomParameters
        , sentenceAxiomPattern
        , sentenceAxiomAttributes = Attributes []
        }

mkAxiom_ :: Validated.Pattern variable -> SentenceAxiom (Validated.Pattern variable)
mkAxiom_ = mkAxiom []

mkSymbol ::
    Id ->
    [SortVariable] ->
    [Sort] ->
    Sort ->
    SentenceSymbol
mkSymbol symbolConstructor symbolParams argumentSorts resultSort' =
    SentenceSymbol
        { sentenceSymbolSymbol =
            Sentence.Symbol
                { symbolConstructor
                , symbolParams
                }
        , sentenceSymbolSorts = argumentSorts
        , sentenceSymbolResultSort = resultSort'
        , sentenceSymbolAttributes = Attributes []
        }

mkSymbol_ ::
    Id ->
    [Sort] ->
    Sort ->
    SentenceSymbol
mkSymbol_ symbolConstructor = mkSymbol symbolConstructor []

applySymbol ::
    HasCallStack =>
    InternalVariable variable =>
    -- | 'Symbol' declaration
    SentenceSymbol ->
    -- | 'Symbol' sort parameters
    [Sort] ->
    -- | 'Application' arguments
    [Validated.Pattern variable] ->
    Validated.Pattern variable
applySymbol sentence params children =
    Validated.updateCallStack $ Validated.mkApplySymbol internal children
  where
    SentenceSymbol{sentenceSymbolSymbol = external} = sentence
    Sentence.Symbol{symbolConstructor} = external
    internal =
        Internal.Symbol
            { Internal.symbolConstructor
            , Internal.symbolParams = params
            , Internal.symbolAttributes = def
            , Internal.symbolSorts =
                symbolOrAliasSorts params sentence
                    & assertRight
            }
