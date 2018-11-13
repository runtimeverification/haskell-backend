module Test.Kore.Step.Step (test_simpleStrategy, test_stepStrategy) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Data.Default
                 ( def )
import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock

import           Data.Limit
                 ( Limit (..) )
import qualified Data.Limit as Limit
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
                 ( MetadataTools (..), SymbolOrAliasSorts )
import qualified Kore.IndexedModule.MetadataTools as HeadType
                 ( HeadType (..) )
import           Kore.MetaML.AST
                 ( CommonMetaPattern )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.BaseStep
import           Kore.Step.ExpandedPattern as ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern, Predicated (..) )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..), evalSimplifier )
import qualified Kore.Step.Simplification.Simplifier as Simplifier
import           Kore.Step.Step
import           Kore.Step.StepperAttributes
import           Kore.Unification.Unifier
                 ( UnificationProof (..) )
import qualified SMT

import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSimplifiers as Mock
import           Test.Tasty.HUnit.Extensions

v1 :: MetaSort sort => sort -> MetaVariable sort
v1 = metaVariable "#v1" AstLocationTest
a1 :: MetaSort sort => sort -> MetaVariable sort
a1 = metaVariable "#a1" AstLocationTest
b1 :: MetaSort sort => sort -> MetaVariable sort
b1 = metaVariable "#b1" AstLocationTest
x1 :: MetaSort sort => sort -> MetaVariable sort
x1 = metaVariable "#x1" AstLocationTest

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

expectTwoAxioms :: [(ExpandedPattern Meta Variable, StepProof Meta Variable)]
expectTwoAxioms =
    [
        ( Predicated
            { term = asPureMetaPattern (v1 PatternSort)
            , predicate = makeTruePredicate
            , substitution = []
            }
        , (mconcat . map stepProof)
            [ StepProofVariableRenamings []
            , StepProofUnification EmptyUnificationProof
            , StepProofSimplification SimplificationProof
            ]
        )
    ,
        ( Predicated
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
            [ StepProofVariableRenamings []
            , StepProofUnification EmptyUnificationProof
            , StepProofSimplification SimplificationProof
            ]
        )
    ]

actualTwoAxioms :: IO [(CommonExpandedPattern Meta, StepProof Meta Variable)]
actualTwoAxioms =
    runStep
        mockMetadataTools
        Predicated
            { term = asPureMetaPattern (v1 PatternSort)
            , predicate = makeTruePredicate
            , substitution = []
            }
        [ rewriteIdentity
        , rewriteImplies
        ]

initialFailSimple :: ExpandedPattern Meta Variable
initialFailSimple =
    Predicated
        { term =
            asPureMetaPattern
                ( metaSigma
                    (metaG (a1 PatternSort))
                    (metaF (b1 PatternSort))
                )
        , predicate = makeTruePredicate
        , substitution = []
        }

expectFailSimple :: [(CommonExpandedPattern Meta, StepProof Meta Variable)]
expectFailSimple = [ (initialFailSimple, mempty) ]

actualFailSimple :: IO [(CommonExpandedPattern Meta, StepProof Meta Variable)]
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
    Predicated
        { term =
            asPureMetaPattern
                ( metaSigma
                    (a1 PatternSort)
                    (a1 PatternSort)
                )
        , predicate = makeTruePredicate
        , substitution = []
        }

expectFailCycle :: [(CommonExpandedPattern Meta, StepProof Meta Variable)]
expectFailCycle = [ (initialFailCycle, mempty) ]

actualFailCycle :: IO [(CommonExpandedPattern Meta, StepProof Meta Variable)]
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
    Predicated
        { term = asPureMetaPattern (v1 PatternSort)
        , predicate = makeTruePredicate
        , substitution = []
        }

expectIdentity :: [(CommonExpandedPattern Meta, StepProof Meta Variable)]
expectIdentity =
    [
        ( initialIdentity
        , (mconcat . map stepProof)
            [ StepProofVariableRenamings []
            , StepProofUnification EmptyUnificationProof
            , StepProofSimplification SimplificationProof
            ]
        )
    ]

actualIdentity :: IO [(CommonExpandedPattern Meta, StepProof Meta Variable)]
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
        (assertEqualWithExplanation "" expectIdentity =<< actualIdentity)
    , testCase "Applies two simple axioms"
        -- Axiom: X1 => X1
        -- Axiom: X1 => implies(X1, X1)
        -- Start pattern: V1
        -- Expected: V1
        -- Expected: implies(V1, V1)
        (assertEqualWithExplanation "" expectTwoAxioms =<< actualTwoAxioms)
    , testCase "Fails to apply a simple axiom"
        -- Axiom: sigma(X1, X1) => X1
        -- Start pattern: sigma(f(A1), g(B1))
        -- Expected: empty result list
        (assertEqualWithExplanation "" expectFailSimple =<< actualFailSimple)
    , testCase "Fails to apply a simple axiom due to cycle."
        -- Axiom: sigma(f(X1), X1) => X1
        -- Start pattern: sigma(A1, A1)
        -- Expected: empty result list
        (assertEqualWithExplanation "" expectFailCycle =<< actualFailCycle)
    ]

test_simpleStrategy :: [TestTree]
test_simpleStrategy =
    [ testCase "Runs one step"
        -- Axiom: f(X1) => g(X1)
        -- Start pattern: f(V1)
        -- Expected: g(V1)
        (assertEqualWithExplanation "" expectOneStep =<< actualOneStep)
    , testCase "Runs two steps"
        -- Axiom: f(X1) => g(X1)
        -- Axiom: g(X1) => h(X1)
        -- Start pattern: f(V1)
        -- Expected: h(V1)
        (assertEqualWithExplanation "" expectTwoSteps =<< actualTwoSteps)
    , testCase "Obeys step limit"
        -- Axiom: f(X1) => g(X1)
        -- Axiom: g(X1) => h(X1)
        -- Start pattern: f(V1)
        -- Expected: g(V1)
        (assertEqualWithExplanation "" expectStepLimit =<< actualStepLimit)
    , testCase "0 step limit"
        -- Axiom: f(X1) => g(X1)
        -- Axiom: g(X1) => h(X1)
        -- Start pattern: f(V1)
        -- Expected: f(V1)
        (assertEqualWithExplanation "" expectZeroStepLimit
            =<< actualZeroStepLimit)
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

expectOneStep :: (ExpandedPattern Meta Variable, StepProof Meta Variable)
expectOneStep =
    ( Predicated
        { term = asPureMetaPattern (metaG (v1 PatternSort))
        , predicate = makeTruePredicate
        , substitution = []
        }
    , mconcat
        (map stepProof
            [ StepProofVariableRenamings []
            , StepProofUnification EmptyUnificationProof
            , StepProofSimplification SimplificationProof
            ]
        )
    )

actualOneStep :: IO (CommonExpandedPattern Meta, StepProof Meta Variable)
actualOneStep =
    runSteps
        mockMetadataTools
        Unlimited
        Predicated
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

expectTwoSteps :: (ExpandedPattern Meta Variable, StepProof Meta Variable)
expectTwoSteps =
    ( Predicated
        { term = asPureMetaPattern (metaH (v1 PatternSort))
        , predicate = makeTruePredicate
        , substitution = []
        }
    , (mconcat . map stepProof)
        [ StepProofVariableRenamings []
        , StepProofUnification EmptyUnificationProof
        , StepProofSimplification SimplificationProof
        , StepProofVariableRenamings []
        , StepProofUnification EmptyUnificationProof
        , StepProofSimplification SimplificationProof
        ]
    )

actualTwoSteps :: IO (CommonExpandedPattern Meta, StepProof Meta Variable)
actualTwoSteps =
    runSteps
        mockMetadataTools
        Unlimited
        Predicated
            { term = asPureMetaPattern (metaF (v1 PatternSort))
            , predicate = makeTruePredicate
            , substitution = []
            }
        axiomsSimpleStrategy


expectZeroStepLimit :: (ExpandedPattern Meta Variable, StepProof Meta Variable)
expectZeroStepLimit =
        ( Predicated
            { term = asPureMetaPattern (metaF (v1 PatternSort))
            , predicate = makeTruePredicate
            , substitution = []
            }
        , mempty
        )

actualZeroStepLimit :: IO (CommonExpandedPattern Meta, StepProof Meta Variable)
actualZeroStepLimit =
    runSteps
        mockMetadataTools
        (Limit 0)
        Predicated
            { term = asPureMetaPattern (metaF (v1 PatternSort))
            , predicate = makeTruePredicate
            , substitution = []
            }
        axiomsSimpleStrategy

expectStepLimit :: (ExpandedPattern Meta Variable, StepProof Meta Variable)
expectStepLimit =
    ( Predicated
        { term = asPureMetaPattern (metaG (v1 PatternSort))
        , predicate = makeTruePredicate
        , substitution = []
        }
    , (mconcat . map stepProof)
        [ StepProofVariableRenamings []
        , StepProofUnification EmptyUnificationProof
        , StepProofSimplification SimplificationProof
        ]
    )

actualStepLimit :: IO (CommonExpandedPattern Meta, StepProof Meta Variable)
actualStepLimit =
    runSteps
        mockMetadataTools
        (Limit 1)
        Predicated
            { term = asPureMetaPattern (metaF (v1 PatternSort))
            , predicate = makeTruePredicate
            , substitution = []
            }
        axiomsSimpleStrategy

mockSymbolOrAliasSorts :: SymbolOrAliasSorts Meta
mockSymbolOrAliasSorts = const ApplicationSorts
    { applicationSortsOperands = [asAst PatternSort, asAst PatternSort]
    , applicationSortsResult = asAst PatternSort
    }

mockMetadataTools :: MetadataTools Meta StepperAttributes
mockMetadataTools = MetadataTools
    { symAttributes = const Mock.constructorFunctionalAttributes
    , symbolOrAliasType = const HeadType.Symbol
    , sortAttributes = const Mock.constructorFunctionalAttributes
    , symbolOrAliasSorts = mockSymbolOrAliasSorts
    , isSubsortOf = const $ const False
    , subsorts = Set.singleton
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

runStep
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -- ^functions yielding metadata for pattern heads
    -> CommonExpandedPattern level
    -- ^left-hand-side of unification
    -> [AxiomPattern level]
    -> IO [(CommonExpandedPattern level, StepProof level Variable)]
runStep metadataTools configuration axioms =
    (<$>) pickFinal
    $ SMT.runSMT SMT.defaultConfig
    $ evalSimplifier
    $ runStrategy
        (transitionRule
            metadataTools
            (Mock.substitutionSimplifier metadataTools)
            simplifier
        )
        [allAxioms axioms]
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
    -> IO (CommonExpandedPattern level, StepProof level Variable)
runSteps metadataTools stepLimit configuration axioms =
    (<$>) pickLongest
    $ SMT.runSMT SMT.defaultConfig
    $ evalSimplifier
    $ runStrategy
        (transitionRule
            metadataTools
            (Mock.substitutionSimplifier metadataTools)
            simplifier
        )
        (Limit.replicate stepLimit $ allAxioms axioms)
        (configuration, mempty)
  where
    simplifier = Simplifier.create metadataTools Map.empty
