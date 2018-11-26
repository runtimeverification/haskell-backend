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
import           Kore.AST.MetaOrObject
import           Kore.ASTHelpers
                 ( ApplicationSorts (..) )
import           Kore.ASTUtils.SmartPatterns
import           Kore.Implicit.ImplicitSorts
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), SymbolOrAliasSorts )
import qualified Kore.IndexedModule.MetadataTools as HeadType
                 ( HeadType (..) )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.AxiomPatterns
                 ( RewriteRule (RewriteRule), RulePattern (RulePattern) )
import           Kore.Step.AxiomPatterns as RulePattern
                 ( RulePattern (..) )
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

import           Test.Kore
import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSimplifiers as Mock
import           Test.Tasty.HUnit.Extensions

v1, a1, b1, x1 :: Sort Meta -> Variable Meta
v1 = Variable (testId "#v1")
a1 = Variable (testId "#a1")
b1 = Variable (testId "#b1")
x1 = Variable (testId "#x1")

rewriteIdentity :: RewriteRule Meta
rewriteIdentity =
    RewriteRule RulePattern
        { left = Var_ (x1 patternMetaSort)
        , right = Var_ (x1 patternMetaSort)
        , requires = makeTruePredicate
        , attributes = def
        }

rewriteImplies :: RewriteRule Meta
rewriteImplies =
    RewriteRule $ RulePattern
        { left = Var_ (x1 patternMetaSort)
        , right =
            Implies_
                patternMetaSort
                (Var_ $ x1 patternMetaSort)
                (Var_ $ x1 patternMetaSort)
        , requires = makeTruePredicate
        , attributes = def
        }

expectTwoAxioms :: [(ExpandedPattern Meta Variable, StepProof Meta Variable)]
expectTwoAxioms =
    [
        ( Predicated
            { term = Var_ (v1 patternMetaSort)
            , predicate = makeTruePredicate
            , substitution = mempty
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
                Implies_
                    patternMetaSort
                    (Var_ $ v1 patternMetaSort)
                    (Var_ $ v1 patternMetaSort)
            , predicate = makeTruePredicate
            , substitution = mempty
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
            { term = Var_ (v1 patternMetaSort)
            , predicate = makeTruePredicate
            , substitution = mempty
            }
        [ rewriteIdentity
        , rewriteImplies
        ]

initialFailSimple :: ExpandedPattern Meta Variable
initialFailSimple =
    Predicated
        { term =
            metaSigma
                (metaG (Var_ $ a1 patternMetaSort))
                (metaF (Var_ $ b1 patternMetaSort))
        , predicate = makeTruePredicate
        , substitution = mempty
        }

expectFailSimple :: [(CommonExpandedPattern Meta, StepProof Meta Variable)]
expectFailSimple = [ (initialFailSimple, mempty) ]

actualFailSimple :: IO [(CommonExpandedPattern Meta, StepProof Meta Variable)]
actualFailSimple =
    runStep
        mockMetadataTools
        initialFailSimple
        [ RewriteRule $ RulePattern
            { left =
                metaSigma
                    (Var_ $ x1 patternMetaSort)
                    (Var_ $ x1 patternMetaSort)
            , right =
                Var_ (x1 patternMetaSort)
            , requires = makeTruePredicate
            , attributes = def
            }
        ]

initialFailCycle :: ExpandedPattern Meta Variable
initialFailCycle =
    Predicated
        { term =
            metaSigma
                (Var_ $ a1 patternMetaSort)
                (Var_ $ a1 patternMetaSort)
        , predicate = makeTruePredicate
        , substitution = mempty
        }

expectFailCycle :: [(CommonExpandedPattern Meta, StepProof Meta Variable)]
expectFailCycle = [ (initialFailCycle, mempty) ]

actualFailCycle :: IO [(CommonExpandedPattern Meta, StepProof Meta Variable)]
actualFailCycle =
    runStep
        mockMetadataTools
        initialFailCycle
        [ RewriteRule $ RulePattern
            { left =
                metaSigma
                    (metaF (Var_ $ x1 patternMetaSort))
                    (Var_ $ x1 patternMetaSort)
            , right =
                Var_ (x1 patternMetaSort)
            , requires = makeTruePredicate
            , attributes = def
            }
        ]

initialIdentity :: ExpandedPattern Meta Variable
initialIdentity =
    Predicated
        { term = Var_ (v1 patternMetaSort)
        , predicate = makeTruePredicate
        , substitution = mempty
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

axiomsSimpleStrategy :: [RewriteRule Meta]
axiomsSimpleStrategy =
    [ RewriteRule $ RulePattern
        { left = metaF (Var_ $ x1 patternMetaSort)
        , right = metaG (Var_ $ x1 patternMetaSort)
        , requires = makeTruePredicate
        , attributes = def
        }
    , RewriteRule $ RulePattern
        { left = metaG (Var_ $ x1 patternMetaSort)
        , right = metaH (Var_ $ x1 patternMetaSort)
        , requires = makeTruePredicate
        , attributes = def
        }
    ]

expectOneStep :: (ExpandedPattern Meta Variable, StepProof Meta Variable)
expectOneStep =
    ( Predicated
        { term = metaG (Var_ $ v1 patternMetaSort)
        , predicate = makeTruePredicate
        , substitution = mempty
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
            { term = metaF (Var_ $ v1 patternMetaSort)
            , predicate = makeTruePredicate
            , substitution = mempty
            }
        [ RewriteRule $ RulePattern
            { left = metaF (Var_ $ x1 patternMetaSort)
            , right = metaG (Var_ $ x1 patternMetaSort)
            , requires = makeTruePredicate
            , attributes = def
            }
        ]

expectTwoSteps :: (ExpandedPattern Meta Variable, StepProof Meta Variable)
expectTwoSteps =
    ( Predicated
        { term = metaH (Var_ $ v1 patternMetaSort)
        , predicate = makeTruePredicate
        , substitution = mempty
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
            { term = metaF (Var_ $ v1 patternMetaSort)
            , predicate = makeTruePredicate
            , substitution = mempty
            }
        axiomsSimpleStrategy


expectZeroStepLimit :: (ExpandedPattern Meta Variable, StepProof Meta Variable)
expectZeroStepLimit =
        ( Predicated
            { term = metaF (Var_ $ v1 patternMetaSort)
            , predicate = makeTruePredicate
            , substitution = mempty
            }
        , mempty
        )

actualZeroStepLimit :: IO (CommonExpandedPattern Meta, StepProof Meta Variable)
actualZeroStepLimit =
    runSteps
        mockMetadataTools
        (Limit 0)
        Predicated
            { term = metaF (Var_ $ v1 patternMetaSort)
            , predicate = makeTruePredicate
            , substitution = mempty
            }
        axiomsSimpleStrategy

expectStepLimit :: (ExpandedPattern Meta Variable, StepProof Meta Variable)
expectStepLimit =
    ( Predicated
        { term = metaG (Var_ $ v1 patternMetaSort)
        , predicate = makeTruePredicate
        , substitution = mempty
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
            { term = metaF (Var_ $ v1 patternMetaSort)
            , predicate = makeTruePredicate
            , substitution = mempty
            }
        axiomsSimpleStrategy

mockSymbolOrAliasSorts :: SymbolOrAliasSorts Meta
mockSymbolOrAliasSorts = const ApplicationSorts
    { applicationSortsOperands = [patternMetaSort, patternMetaSort]
    , applicationSortsResult = patternMetaSort
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
    { symbolOrAliasConstructor = testId "#sigma"
    , symbolOrAliasParams = []
    }

metaSigma
    :: CommonPurePattern Meta dom
    -> CommonPurePattern Meta dom
    -> CommonPurePattern Meta dom
metaSigma p1 p2 = App_ sigmaSymbol [p1, p2]


fSymbol :: SymbolOrAlias Meta
fSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = Id "#f" AstLocationTest
    , symbolOrAliasParams = []
    }

metaF
    :: CommonPurePattern Meta dom
    -> CommonPurePattern Meta dom
metaF p = App_ fSymbol [p]


gSymbol :: SymbolOrAlias Meta
gSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = Id "#g" AstLocationTest
    , symbolOrAliasParams = []
    }

metaG
    :: CommonPurePattern Meta dom
    -> CommonPurePattern Meta dom
metaG p = App_ gSymbol [p]


hSymbol :: SymbolOrAlias Meta
hSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = Id "#h" AstLocationTest
    , symbolOrAliasParams = []
    }

metaH
    :: CommonPurePattern Meta dom
    -> CommonPurePattern Meta dom
metaH p = App_ hSymbol [p]

runStep
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -- ^functions yielding metadata for pattern heads
    -> CommonExpandedPattern level
    -- ^left-hand-side of unification
    -> [RewriteRule level]
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
        [allRewrites axioms]
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
    -> [RewriteRule level]
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
        (Limit.replicate stepLimit $ allRewrites axioms)
        (configuration, mempty)
  where
    simplifier = Simplifier.create metadataTools Map.empty
