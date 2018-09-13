module Test.Kore.Step.Step (test_simpleStrategy, test_stepStrategy) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Data.Default
                 ( def )
import qualified Data.Map as Map

import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock

import           Kore.AST.Common
                 ( Application (..), AstLocation (..), Id (..),
                 Pattern (ApplicationPattern), SymbolOrAlias (..), Variable )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureToKore
                 ( patternKoreToPure )
import           Kore.ASTHelpers
                 ( ApplicationSorts (..) )
import           Kore.Building.AsAst
import           Kore.Building.Patterns
import           Kore.Building.Sorts
import           Kore.Error
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), SortTools )
import           Kore.MetaML.AST
                 ( CommonMetaPattern )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.BaseStep
import           Kore.Step.ExpandedPattern as ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern (..) )
import           Kore.Step.PatternAttributes
                 ( FunctionalProof (..) )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..), evalSimplifier )
import qualified Kore.Step.Simplification.Simplifier as Simplifier
import           Kore.Step.Step
import           Kore.Step.StepperAttributes
import           Kore.Unification.Unifier
                 ( UnificationProof (..) )

import Test.Kore.Comparators ()
import Test.Tasty.HUnit.Extensions

v1 :: MetaSort sort => sort -> MetaVariable sort
v1 = metaVariable "#v1" AstLocationTest
a1 :: MetaSort sort => sort -> MetaVariable sort
a1 = metaVariable "#a1" AstLocationTest
b1 :: MetaSort sort => sort -> MetaVariable sort
b1 = metaVariable "#b1" AstLocationTest
x1 :: MetaSort sort => sort -> MetaVariable sort
x1 = metaVariable "#x1" AstLocationTest
var_0 :: MetaSort sort => sort -> MetaVariable sort
var_0 = metaVariable "#var_0" AstLocationTest
var_1 :: MetaSort sort => sort -> MetaVariable sort
var_1 = metaVariable "#var_1" AstLocationTest
var_3 :: MetaSort sort => sort -> MetaVariable sort
var_3 = metaVariable "#var_3" AstLocationTest

rewriteIdentity :: AxiomPattern Meta
rewriteIdentity =
    AxiomPattern
        { axiomPatternLeft = asPureMetaPattern (x1 PatternSort)
        , axiomPatternRight = asPureMetaPattern (x1 PatternSort)
        , axiomPatternRequires = makeTruePredicate
        , axiomPatternAttributes = def
        }

rewriteImplies :: AxiomPattern Meta
rewriteImplies =
    AxiomPattern
        { axiomPatternLeft = asPureMetaPattern (x1 PatternSort)
        , axiomPatternRight =
            asPureMetaPattern
                (metaImplies PatternSort
                    (x1 PatternSort)
                    (x1 PatternSort)
                )
        , axiomPatternRequires = makeTruePredicate
        , axiomPatternAttributes = def
        }

expectTwoAxioms :: [(ExpandedPattern Meta Variable, StepProof Meta)]
expectTwoAxioms =
    [
        ( ExpandedPattern
            { term = asPureMetaPattern (v1 PatternSort)
            , predicate = makeTruePredicate
            , substitution = []
            }
        , (mconcat . map stepProof)
            [ StepProofVariableRenamings
                [ variableRenaming
                    (x1 PatternSort) (var_0 PatternSort)
                ]
            , StepProofUnification
                ( proposition_5_24_3
                    [ functionalVariable (v1 PatternSort) ]
                    (var_0 PatternSort)
                    (v1 PatternSort)
                )
            , StepProofSimplification SimplificationProof
            ]
        )
    ,
        ( ExpandedPattern
            { term =
                asPureMetaPattern
                    (metaImplies PatternSort
                        (v1 PatternSort)
                        (v1 PatternSort)
                    )
            , predicate = makeTruePredicate
            , substitution = []
            }
        , (mconcat . map stepProof)
            [ StepProofVariableRenamings
                [ variableRenaming
                    (x1 PatternSort) (var_1 PatternSort)
                ]
            , StepProofUnification
                ( proposition_5_24_3
                    [ functionalVariable (v1 PatternSort) ]
                    (var_1 PatternSort)
                    (v1 PatternSort)
                )
            , StepProofSimplification SimplificationProof
            ]
        )
    ]

actualTwoAxioms :: [(CommonExpandedPattern Meta, StepProof Meta)]
actualTwoAxioms =
    runStep
        mockMetadataTools
        ExpandedPattern
            { term = asPureMetaPattern (v1 PatternSort)
            , predicate = makeTruePredicate
            , substitution = []
            }
        [ rewriteIdentity
        , rewriteImplies
        ]

initialFailSimple :: ExpandedPattern Meta Variable
initialFailSimple =
    ExpandedPattern
        { term =
            asPureMetaPattern
                ( metaSigma
                    (metaG (a1 PatternSort))
                    (metaF (b1 PatternSort))
                )
        , predicate = makeTruePredicate
        , substitution = []
        }

expectFailSimple :: [(CommonExpandedPattern Meta, StepProof Meta)]
expectFailSimple = [ (initialFailSimple, mempty) ]

actualFailSimple :: [(CommonExpandedPattern Meta, StepProof Meta)]
actualFailSimple =
    runStep
        mockMetadataTools
        initialFailSimple
        [ AxiomPattern
            { axiomPatternLeft =
                asPureMetaPattern
                    (metaSigma (x1 PatternSort) (x1 PatternSort))
            , axiomPatternRight =
                asPureMetaPattern (x1 PatternSort)
            , axiomPatternRequires = makeTruePredicate
            , axiomPatternAttributes = def
            }
        ]

initialFailCycle :: ExpandedPattern Meta Variable
initialFailCycle =
    ExpandedPattern
        { term =
            asPureMetaPattern
                ( metaSigma
                    (a1 PatternSort)
                    (a1 PatternSort)
                )
        , predicate = makeTruePredicate
        , substitution = []
        }

expectFailCycle :: [(CommonExpandedPattern Meta, StepProof Meta)]
expectFailCycle = [ (initialFailCycle, mempty) ]

actualFailCycle :: [(CommonExpandedPattern Meta, StepProof Meta)]
actualFailCycle =
    runStep
        mockMetadataTools
        initialFailCycle
        [ AxiomPattern
            { axiomPatternLeft =
                asPureMetaPattern
                    (metaSigma
                        (metaF (x1 PatternSort))
                        (x1 PatternSort)
                    )
            , axiomPatternRight =
                asPureMetaPattern (x1 PatternSort)
            , axiomPatternRequires = makeTruePredicate
            , axiomPatternAttributes = def
            }
        ]

initialIdentity :: ExpandedPattern Meta Variable
initialIdentity =
    ExpandedPattern
        { term = asPureMetaPattern (v1 PatternSort)
        , predicate = makeTruePredicate
        , substitution = []
        }

expectIdentity :: [(CommonExpandedPattern Meta, StepProof Meta)]
expectIdentity =
    [
        ( initialIdentity
        , (mconcat . map stepProof)
            [ StepProofVariableRenamings
                [ variableRenaming (x1 PatternSort) (var_0 PatternSort) ]
            , StepProofUnification
                ( proposition_5_24_3
                    [ functionalVariable (v1 PatternSort) ]
                    (var_0 PatternSort)
                    (v1 PatternSort)
                )
            , StepProofSimplification SimplificationProof
            ]
        )
    ]

actualIdentity :: [(CommonExpandedPattern Meta, StepProof Meta)]
actualIdentity =
    runStep
        mockMetadataTools
        initialIdentity
        [ rewriteIdentity ]

test_stepStrategy :: [TestTree]
test_stepStrategy =
    [ testCase "Applies a simple axiom"
        -- Axiom: X1 => X1
        -- Start pattern: V1
        -- Expected: V1
        (assertEqualWithExplanation "" expectIdentity actualIdentity)
    , testCase "Applies two simple axioms"
        -- Axiom: X1 => X1
        -- Axiom: X1 => implies(X1, X1)
        -- Start pattern: V1
        -- Expected: V1
        -- Expected: implies(V1, V1)
        (assertEqualWithExplanation "" expectTwoAxioms actualTwoAxioms)
    , testCase "Fails to apply a simple axiom"
        -- Axiom: sigma(X1, X1) => X1
        -- Start pattern: sigma(f(A1), g(B1))
        -- Expected: empty result list
        (assertEqualWithExplanation "" expectFailSimple actualFailSimple)
    , testCase "Fails to apply a simple axiom due to cycle."
        -- Axiom: sigma(f(X1), X1) => X1
        -- Start pattern: sigma(A1, A1)
        -- Expected: empty result list
        (assertEqualWithExplanation "" expectFailCycle actualFailCycle)
    ]

test_simpleStrategy :: [TestTree]
test_simpleStrategy =
    [ testCase "Runs one step"
        -- Axiom: f(X1) => g(X1)
        -- Start pattern: f(V1)
        -- Expected: g(V1)
        (assertEqualWithExplanation "" expectOneStep actualOneStep)
    , testCase "Runs two steps"
        -- Axiom: f(X1) => g(X1)
        -- Axiom: g(X1) => h(X1)
        -- Start pattern: f(V1)
        -- Expected: h(V1)
        (assertEqualWithExplanation "" expectTwoSteps actualTwoSteps)
    , testCase "Obeys step limit"
        -- Axiom: f(X1) => g(X1)
        -- Axiom: g(X1) => h(X1)
        -- Start pattern: f(V1)
        -- Expected: g(V1)
        (assertEqualWithExplanation "" expectStepLimit actualStepLimit)
    , testCase "0 step limit"
        -- Axiom: f(X1) => g(X1)
        -- Axiom: g(X1) => h(X1)
        -- Start pattern: f(V1)
        -- Expected: f(V1)
        (assertEqualWithExplanation "" expectZeroStepLimit actualZeroStepLimit)
    ]

axiomsSimpleStrategy :: [AxiomPattern Meta]
axiomsSimpleStrategy =
    [ AxiomPattern
        { axiomPatternLeft =
            asPureMetaPattern (metaF (x1 PatternSort))
        , axiomPatternRight =
            asPureMetaPattern (metaG (x1 PatternSort))
        , axiomPatternRequires = makeTruePredicate
        , axiomPatternAttributes = def
        }
    , AxiomPattern
        { axiomPatternLeft =
            asPureMetaPattern (metaG (x1 PatternSort))
        , axiomPatternRight =
            asPureMetaPattern (metaH (x1 PatternSort))
        , axiomPatternRequires = makeTruePredicate
        , axiomPatternAttributes = def
        }
    ]

expectOneStep :: (ExpandedPattern Meta Variable, StepProof Meta)
expectOneStep =
    ( ExpandedPattern
        { term = asPureMetaPattern (metaG (v1 PatternSort))
        , predicate = makeTruePredicate
        , substitution = []
        }
    , mconcat
        (map stepProof
            [ StepProofVariableRenamings
                [ variableRenaming
                    (x1 PatternSort) (var_0 PatternSort)
                ]
            , StepProofUnification
                (AndDistributionAndConstraintLifting
                    fSymbol
                    [ proposition_5_24_3
                        [ functionalVariable (v1 PatternSort) ]
                        (var_0 PatternSort)
                        (v1 PatternSort)
                    ]
                )
            , StepProofSimplification SimplificationProof
            ]
        )
    )

actualOneStep :: (CommonExpandedPattern Meta, StepProof Meta)
actualOneStep =
    runSteps
        mockMetadataTools
        Unlimited
        ExpandedPattern
            { term = asPureMetaPattern (metaF (v1 PatternSort))
            , predicate = makeTruePredicate
            , substitution = []
            }
        [ AxiomPattern
            { axiomPatternLeft =
                asPureMetaPattern (metaF (x1 PatternSort))
            , axiomPatternRight =
                asPureMetaPattern (metaG (x1 PatternSort))
            , axiomPatternRequires = makeTruePredicate
            , axiomPatternAttributes = def
            }
        ]

expectTwoSteps :: (ExpandedPattern Meta Variable, StepProof Meta)
expectTwoSteps =
    ( ExpandedPattern
        { term = asPureMetaPattern (metaH (v1 PatternSort))
        , predicate = makeTruePredicate
        , substitution = []
        }
    , (mconcat . map stepProof)
        [ StepProofVariableRenamings
            [ variableRenaming
                (x1 PatternSort) (var_0 PatternSort)
            ]
        , StepProofUnification
            (AndDistributionAndConstraintLifting
                fSymbol
                [ proposition_5_24_3
                    [ functionalVariable (v1 PatternSort) ]
                    (var_0 PatternSort)
                    (v1 PatternSort)
                ]
            )
        , StepProofSimplification SimplificationProof
        , StepProofVariableRenamings
            [ variableRenaming
                (x1 PatternSort) (var_3 PatternSort)
            ]
        , StepProofUnification
            (AndDistributionAndConstraintLifting
                gSymbol
                [ proposition_5_24_3
                    [ functionalVariable (v1 PatternSort) ]
                    (var_3 PatternSort)
                    (v1 PatternSort)
                ]
            )
        , StepProofSimplification SimplificationProof
        ]
    )

actualTwoSteps :: (CommonExpandedPattern Meta, StepProof Meta)
actualTwoSteps =
    runSteps
        mockMetadataTools
        Unlimited
        ExpandedPattern
            { term = asPureMetaPattern (metaF (v1 PatternSort))
            , predicate = makeTruePredicate
            , substitution = []
            }
        axiomsSimpleStrategy


expectZeroStepLimit :: (ExpandedPattern Meta Variable, StepProof Meta)
expectZeroStepLimit =
        ( ExpandedPattern
            { term = asPureMetaPattern (metaF (v1 PatternSort))
            , predicate = makeTruePredicate
            , substitution = []
            }
        , mempty
        )

actualZeroStepLimit :: (CommonExpandedPattern Meta, StepProof Meta)
actualZeroStepLimit =
    runSteps
        mockMetadataTools
        (Limit 0)
        ExpandedPattern
            { term = asPureMetaPattern (metaF (v1 PatternSort))
            , predicate = makeTruePredicate
            , substitution = []
            }
        axiomsSimpleStrategy

expectStepLimit :: (ExpandedPattern Meta Variable, StepProof Meta)
expectStepLimit =
    ( ExpandedPattern
        { term = asPureMetaPattern (metaG (v1 PatternSort))
        , predicate = makeTruePredicate
        , substitution = []
        }
    , (mconcat . map stepProof)
        [ StepProofVariableRenamings
            [ variableRenaming
                (x1 PatternSort) (var_0 PatternSort)
            ]
        , StepProofUnification
            (AndDistributionAndConstraintLifting
                fSymbol
                [ proposition_5_24_3
                    [ functionalVariable (v1 PatternSort) ]
                    (var_0 PatternSort)
                    (v1 PatternSort)
                ]
            )
        , StepProofSimplification SimplificationProof
        ]
    )

actualStepLimit :: (CommonExpandedPattern Meta, StepProof Meta)
actualStepLimit =
    runSteps
        mockMetadataTools
        (Limit 1)
        ExpandedPattern
            { term = asPureMetaPattern (metaF (v1 PatternSort))
            , predicate = makeTruePredicate
            , substitution = []
            }
        axiomsSimpleStrategy

mockSortTools :: SortTools Meta
mockSortTools = const ApplicationSorts
    { applicationSortsOperands = [asAst PatternSort, asAst PatternSort]
    , applicationSortsResult = asAst PatternSort
    }

mockMetadataTools :: MetadataTools Meta StepperAttributes
mockMetadataTools = MetadataTools
    { symAttributes = const Mock.constructorFunctionalAttributes
    , sortAttributes = const Mock.constructorFunctionalAttributes
    , sortTools = mockSortTools
    }


sigmaSymbol :: SymbolOrAlias Meta
sigmaSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = Id "#sigma" AstLocationTest
    , symbolOrAliasParams = []
    }

data MetaSigma p1 p2 = MetaSigma p1 p2
instance (MetaPattern PatternSort p1, MetaPattern PatternSort p2)
    => ProperPattern Meta PatternSort (MetaSigma p1 p2)
  where
    asProperPattern (MetaSigma p1 p2) =
        ApplicationPattern Application
            { applicationSymbolOrAlias = sigmaSymbol
            , applicationChildren = [asAst p1, asAst p2]
            }
metaSigma
    :: (MetaPattern PatternSort p1, MetaPattern PatternSort p2)
    => p1 -> p2 -> MetaSigma p1 p2
metaSigma = MetaSigma


fSymbol :: SymbolOrAlias Meta
fSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = Id "#f" AstLocationTest
    , symbolOrAliasParams = []
    }

newtype MetaF p1 = MetaF p1
instance (MetaPattern PatternSort p1)
    => ProperPattern Meta PatternSort (MetaF p1)
  where
    asProperPattern (MetaF p1) =
        ApplicationPattern Application
            { applicationSymbolOrAlias = fSymbol
            , applicationChildren = [asAst p1]
            }
metaF
    :: (MetaPattern PatternSort p1)
    => p1 -> MetaF p1
metaF = MetaF


gSymbol :: SymbolOrAlias Meta
gSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = Id "#g" AstLocationTest
    , symbolOrAliasParams = []
    }

newtype MetaG p1 = MetaG p1
instance (MetaPattern PatternSort p1)
    => ProperPattern Meta PatternSort (MetaG p1)
  where
    asProperPattern (MetaG p1) =
        ApplicationPattern Application
            { applicationSymbolOrAlias = gSymbol
            , applicationChildren = [asAst p1]
            }
metaG
    :: (MetaPattern PatternSort p1)
    => p1 -> MetaG p1
metaG = MetaG


hSymbol :: SymbolOrAlias Meta
hSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = Id "#h" AstLocationTest
    , symbolOrAliasParams = []
    }

newtype MetaH p1 = MetaH p1
instance (MetaPattern PatternSort p1)
    => ProperPattern Meta PatternSort (MetaH p1)
  where
    asProperPattern (MetaH p1) =
        ApplicationPattern Application
            { applicationSymbolOrAlias = hSymbol
            , applicationChildren = [asAst p1]
            }
metaH
    :: (MetaPattern PatternSort p1)
    => p1 -> MetaH p1
metaH = MetaH

asPureMetaPattern
    :: ProperPattern Meta sort patt => patt -> CommonMetaPattern
asPureMetaPattern patt =
    case patternKoreToPure Meta (asAst patt) of
        Left err  -> error (printError err)
        Right pat -> pat

variableRenaming
    :: MetaSort sort
    => MetaVariable sort -> MetaVariable sort -> VariableRenaming Meta
variableRenaming from to =
    VariableRenaming
        { variableRenamingOriginal = AxiomVariable (asMetaVariable from)
        , variableRenamingRenamed =
            ConfigurationVariable (asMetaVariable to)
        }

proposition_5_24_3
    :: (MetaSort sort1, ProperPattern Meta sort2 patt)
    => [FunctionalProof Meta Variable]
    -> MetaVariable sort1
    -> patt
    -> UnificationProof Meta Variable
proposition_5_24_3 functionalProof variable patt =
    Proposition_5_24_3
        functionalProof
        (asMetaVariable variable)
        (asPureMetaPattern patt)

functionalVariable
    :: MetaSort sort => MetaVariable sort -> FunctionalProof Meta Variable
functionalVariable = FunctionalVariable . asMetaVariable

runStep
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -- ^functions yielding metadata for pattern heads
    -> CommonExpandedPattern level
    -- ^left-hand-side of unification
    -> [AxiomPattern level]
    -> [(CommonExpandedPattern level, StepProof level)]
runStep metadataTools configuration axioms =
    evalSimplifier
        $ stepStepper
            metadataTools
            simplifier
            axioms
            (configuration, mempty)
  where
    simplifier = Simplifier.create metadataTools Map.empty

runSteps
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -- ^functions yielding metadata for pattern heads
    -> Limit Natural
    -> CommonExpandedPattern level
    -- ^left-hand-side of unification
    -> [AxiomPattern level]
    -> (CommonExpandedPattern level, StepProof level)
runSteps metadataTools stepLimit configuration axioms =
    evalSimplifier
        $ simpleStepper
            metadataTools
            simplifier
            axioms
            stepLimit
            (configuration, mempty)
  where
    simplifier = Simplifier.create metadataTools Map.empty
