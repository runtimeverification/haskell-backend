module Test.Kore.Step.Step
    ( test_simpleStrategy
    , test_stepStrategy
    , test_onePathStrategy
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Data.Default
                 ( def )
import qualified Data.Map as Map
import           Data.Maybe
                 ( fromMaybe )
import           Data.Reflection
                 ( give )
import qualified Data.Set as Set
import           Data.Tree
                 ( Tree )

import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock

import           Data.Limit
                 ( Limit (..) )
import qualified Data.Limit as Limit
import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.ASTHelpers
                 ( ApplicationSorts (..) )
import           Kore.ASTUtils.SmartConstructors
                 ( mkBottom, mkVar )
import           Kore.ASTUtils.SmartPatterns
import           Kore.Implicit.ImplicitSorts
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), SymbolOrAliasSorts )
import qualified Kore.IndexedModule.MetadataTools as HeadType
                 ( HeadType (..) )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeEqualsPredicate, makeNotPredicate,
                 makeTruePredicate )
import           Kore.Step.AxiomPatterns
                 ( RewriteRule (RewriteRule), RulePattern (RulePattern) )
import           Kore.Step.AxiomPatterns as RulePattern
                 ( RulePattern (..) )
import           Kore.Step.BaseStep
import           Kore.Step.ExpandedPattern as ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern, Predicated (..),
                 fromPurePattern )
import           Kore.Step.Pattern
                 ( CommonStepPattern )
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
import qualified Test.Kore.Step.MockSymbols as Mock
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

test_onePathStrategy :: [TestTree]
test_onePathStrategy = give symbolOrAliasSorts
    [ testCase "Runs zero steps" $ do
        -- Removal axiom: a => bottom
        -- Coinductive axiom: a => b
        -- Normal axiom: a => c
        -- Start pattern: a
        -- Expected: a
        [(actual, _proof)] <- runOnePathSteps
            metadataTools
            (Limit 0)
            (ExpandedPattern.fromPurePattern Mock.a)
            (simpleAxiom Mock.a mkBottom)
            [simpleAxiom Mock.a Mock.b]
            [simpleAxiom Mock.a Mock.c]
        assertEqualWithExplanation ""
            (ExpandedPattern.fromPurePattern Mock.a)
            actual
    , testCase "Axiom priority, first step" $ do
        -- Removal axiom: a => bottom
        -- Coinductive axiom: a => b
        -- Normal axiom: a => c
        -- Start pattern: a
        -- Expected: a, since a->bottom and bottom is ignored
        [(_actual, _proof)] <- runOnePathSteps
            metadataTools
            (Limit 1)
            (ExpandedPattern.fromPurePattern Mock.a)
            (simpleAxiom Mock.a mkBottom)
            [simpleAxiom Mock.a Mock.b]
            [simpleAxiom Mock.a Mock.c]
        assertEqualWithExplanation ""
            (ExpandedPattern.fromPurePattern Mock.a)
            _actual
        -- Removal axiom: d => bottom
        -- Coinductive axiom: a => b
        -- Normal axiom: a => c
        -- Start pattern: a
        -- Expected: c, since coinductive axioms are applied only at the second
        -- step
        [(_actual, _proof)] <- runOnePathSteps
            metadataTools
            (Limit 1)
            (ExpandedPattern.fromPurePattern Mock.a)
            (simpleAxiom Mock.d mkBottom)
            [simpleAxiom Mock.a Mock.b]
            [simpleAxiom Mock.a Mock.c]
        assertEqualWithExplanation ""
            (ExpandedPattern.fromPurePattern Mock.c)
            _actual
    , testCase "Axiom priority, second step" $ do
        -- Removal axiom: b => bottom
        -- Coinductive axiom: b => c
        -- Normal axiom: b => d
        -- Normal axiom: a => b
        -- Start pattern: a
        -- Expected: b, since a->b->bottom and bottom is ignored
        [(_actual, _proof)] <- runOnePathSteps
            metadataTools
            (Limit 2)
            (ExpandedPattern.fromPurePattern Mock.a)
            (simpleAxiom Mock.b mkBottom)
            [simpleAxiom Mock.b Mock.c]
            [ simpleAxiom Mock.b Mock.d
            , simpleAxiom Mock.a Mock.b
            ]
        assertEqualWithExplanation ""
            (ExpandedPattern.fromPurePattern Mock.b)
            _actual
        -- Removal axiom: e => bottom
        -- Coinductive axiom: b => c
        -- Normal axiom: b => d
        -- Normal axiom: a => b
        -- Start pattern: a
        -- Expected: c, since a->b->c and b->d is ignored
        [(_actual, _proof)] <- runOnePathSteps
            metadataTools
            (Limit 2)
            (ExpandedPattern.fromPurePattern Mock.a)
            (simpleAxiom Mock.e mkBottom)
            [simpleAxiom Mock.b Mock.c]
            [ simpleAxiom Mock.b Mock.d
            , simpleAxiom Mock.a Mock.b
            ]
        assertEqualWithExplanation ""
            (ExpandedPattern.fromPurePattern Mock.c)
            _actual
        -- Removal axiom: e => bottom
        -- Coinductive axiom: e => c
        -- Normal axiom: b => d
        -- Normal axiom: a => b
        -- Start pattern: a
        -- Expected: c, since a->b->c and b->d is ignored
        [(_actual, _proof)] <- runOnePathSteps
            metadataTools
            (Limit 2)
            (ExpandedPattern.fromPurePattern Mock.a)
            (simpleAxiom Mock.e mkBottom)
            [simpleAxiom Mock.e Mock.c]
            [ simpleAxiom Mock.b Mock.d
            , simpleAxiom Mock.a Mock.b
            ]
        assertEqualWithExplanation ""
            (ExpandedPattern.fromPurePattern Mock.d)
            _actual
    , testCase "Differentiated axioms" $ do
        -- Removal axiom: constr11(a) => f(a)
        -- Coinductive axiom: constr11(a) => g(a)
        -- Coinductive axiom: constr11(b) => f(b)
        -- Normal axiom: constr11(a) => g(a)
        -- Normal axiom: constr11(b) => g(b)
        -- Normal axiom: constr11(c) => f(c)
        -- Normal axiom: constr11(x) => h(x)
        -- Normal axiom: constr10(x) => constr11(x)
        -- Start pattern: constr10(x)
        -- Expected:
        --   f(a) and x=a
        --   or (f(b) and x=b)
        --   or (f(c) and x=c)
        --   or (h(x) and x!=a and x!=b and x!=c )
        [ (_actual1, _proof1)
         , (_actual2, _proof2)
         , (_actual3, _proof3)
         , (_actual4, _proof4)
         ] <-
            runOnePathSteps
                metadataTools
                (Limit 2)
                (ExpandedPattern.fromPurePattern
                    (Mock.functionalConstr10 (mkVar Mock.x))
                )
                (simpleAxiom (Mock.functionalConstr11 Mock.a) (Mock.f Mock.a))
                [ simpleAxiom (Mock.functionalConstr11 Mock.a) (Mock.g Mock.a)
                , simpleAxiom (Mock.functionalConstr11 Mock.b) (Mock.f Mock.b)
                ]
                [ simpleAxiom (Mock.functionalConstr11 Mock.a) (Mock.g Mock.a)
                , simpleAxiom (Mock.functionalConstr11 Mock.b) (Mock.g Mock.b)
                , simpleAxiom (Mock.functionalConstr11 Mock.c) (Mock.f Mock.c)
                , simpleAxiom
                    (Mock.functionalConstr11 (mkVar Mock.y))
                    (Mock.h (mkVar Mock.y))
                , simpleAxiom
                    (Mock.functionalConstr10 (mkVar Mock.y))
                    (Mock.functionalConstr11 (mkVar Mock.y))
                ]
        assertEqualWithExplanation ""
            Predicated
                { term = Mock.f Mock.a
                , predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.a)]
                }
            _actual1
        assertEqualWithExplanation ""
            Predicated
                { term = Mock.f Mock.b
                , predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.b)]
                }
            _actual2
        assertEqualWithExplanation ""
            Predicated
                { term = Mock.f Mock.c
                , predicate = makeTruePredicate
                , substitution = [(Mock.x, Mock.c)]
                }
            _actual3
        assertEqualWithExplanation ""
            Predicated
                { term = Mock.h (mkVar Mock.x)
                , predicate =  -- TODO(virgil): Better and simplification.
                    makeAndPredicate
                        (makeAndPredicate
                            (makeAndPredicate
                                (makeAndPredicate
                                    (makeNotPredicate
                                        (makeEqualsPredicate
                                            (mkVar Mock.x) Mock.a
                                        )
                                    )
                                    (makeNotPredicate
                                        (makeEqualsPredicate
                                            (mkVar Mock.x) Mock.b
                                        )
                                    )
                                )
                                (makeNotPredicate
                                    (makeEqualsPredicate (mkVar Mock.x) Mock.a)
                                )
                            )
                            (makeNotPredicate
                                (makeEqualsPredicate (mkVar Mock.x) Mock.b)
                            )
                        )
                        (makeNotPredicate
                            (makeEqualsPredicate (mkVar Mock.x) Mock.c)
                        )
                , substitution = []
                }
            _actual4
    ]
  where
    symbolOrAliasSorts :: SymbolOrAliasSorts Object
    symbolOrAliasSorts =
        Mock.makeSymbolOrAliasSorts Mock.symbolOrAliasSortsMapping
    metadataTools :: MetadataTools Object StepperAttributes
    metadataTools =
        Mock.makeMetadataTools
            symbolOrAliasSorts
            Mock.attributesMapping
            Mock.headTypeMapping
            Mock.subsorts

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
    runExecutionSteps
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
    runExecutionSteps
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
    runExecutionSteps
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
    runExecutionSteps
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

simpleRule
    :: MetaOrObject level
    => CommonStepPattern level
    -> CommonStepPattern level
    -> RulePattern level
simpleRule left right =
    RulePattern
        { axiomPatternLeft = left
        , axiomPatternRight = right
        , axiomPatternRequires = makeTruePredicate
        , axiomPatternAttributes = def
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
    $ (fromMaybe (error "Unexpected missing tree") . ruleResultToRewriteTree)
    <$> runStrategy
        (transitionRule
            metadataTools
            (Mock.substitutionSimplifier metadataTools)
            simplifier
        )
        [allRewrites axioms]
        (RewritePattern configuration, mempty)
  where
    simplifier = Simplifier.create metadataTools Map.empty

runSteps
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -- ^functions yielding metadata for pattern heads
    -> (Tree (CommonExpandedPattern level, StepProof level Variable) -> a)
    -> CommonExpandedPattern level
    -- ^left-hand-side of unification
    -> [Strategy (Prim (RewriteRule level))]
    -> IO a
runSteps metadataTools picker configuration strategy =
    (<$>) picker
    $ SMT.runSMT SMT.defaultConfig
    $ evalSimplifier
    $ (fromMaybe (error "Unexpected missing tree") . ruleResultToRewriteTree)
    <$> runStrategy
        (transitionRule
            metadataTools
            (Mock.substitutionSimplifier metadataTools)
            simplifier
        )
        strategy
        (RewritePattern configuration, mempty)
  where
    simplifier = Simplifier.create metadataTools Map.empty

runExecutionSteps
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -- ^functions yielding metadata for pattern heads
    -> Limit Natural
    -> CommonExpandedPattern level
    -- ^left-hand-side of unification
    -> [RewriteRule level]
    -> IO (CommonExpandedPattern level, StepProof level Variable)
runExecutionSteps metadataTools stepLimit configuration rewrites =
    runSteps
        metadataTools
        pickLongest
        configuration
        (Limit.replicate stepLimit $ allRewrites rewrites)

runOnePathSteps
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -- ^functions yielding metadata for pattern heads
    -> Limit Natural
    -> CommonExpandedPattern level
    -- ^left-hand-side of unification
    -> RewriteRule level
    -> [RewriteRule level]
    -> [RewriteRule level]
    -> IO [(CommonExpandedPattern level, StepProof level Variable)]
runOnePathSteps
    metadataTools
    stepLimit
    configuration
    destinationRemovalRewrite
    coinductiveRewrites
    rewrites
  =
    runSteps
        metadataTools
        pickFinal
        configuration
        (Limit.takeWithin
            stepLimit
            ( onePathFirstStep destinationRemovalRewrite rewrites
            : repeat
                (onePathFollowupStep
                    destinationRemovalRewrite
                    coinductiveRewrites
                    rewrites
                )
            )
        )
