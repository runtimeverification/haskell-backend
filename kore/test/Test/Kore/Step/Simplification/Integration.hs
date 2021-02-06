{-# LANGUAGE Strict #-}

module Test.Kore.Step.Simplification.Integration
    ( test_simplificationIntegration
    , test_simplificationIntegrationUnification
    , test_substituteMap
    , test_substituteList
    , test_substitute
    ) where

import Prelude.Kore

import qualified Control.Lens as Lens
import Data.Align
    ( align
    )
import qualified Data.Default as Default
import qualified Data.Foldable as Foldable
import Data.Generics.Product
import qualified Data.Map.Strict as Map
import Data.Maybe
    ( fromJust
    )
import qualified Data.Set as Set
import Test.Tasty

import qualified Kore.Builtin.AssociativeCommutative as Ac
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Builtin.Int as Int
import qualified Kore.Builtin.List as List
import qualified Kore.Builtin.Map as Map
import qualified Kore.Builtin.Set as Set
import Kore.Equation
    ( Equation (..)
    , mkEquation
    )
import qualified Kore.Equation as Equation
import Kore.Internal.InternalSet
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.SideCondition as SideCondition
    ( toRepresentation
    , top
    )
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition
    ( Representation
    )
import Kore.Rewriting.RewritingVariable
    ( RewritingVariableName
    , mkConfigVariable
    , mkRuleVariable
    )
import Kore.Step.Axiom.EvaluationStrategy
    ( builtinEvaluation
    , simplifierWithFallback
    )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
    ( AxiomIdentifier (..)
    )
import Kore.Step.Axiom.Registry
    ( mkEvaluatorRegistry
    )
import qualified Kore.Step.Simplification.Pattern as Pattern
    ( simplify
    )
import Kore.Step.Simplification.Simplify

import Test.Expect
import Test.Kore
import Test.Kore.Equation.Common
    ( functionAxiomUnification
    , functionAxiomUnification_
    )
-- import Test.Kore.Internal.OrPattern
--     ( OrTestPattern
--     )
import qualified Test.Kore.Internal.OrPattern as OrPattern
import Test.Kore.Internal.Pattern
    ( Conditional (..)
    )
import qualified Test.Kore.Internal.Pattern as Pattern
import Test.Kore.Internal.Predicate as Predicate
import Test.Kore.Internal.Substitution as Substitution hiding
    ( test_substitute
    )
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext

type SideCondition' = SideCondition RewritingVariableName

test_simplificationIntegration :: [TestTree]
test_simplificationIntegration =
    [ testCase "owise condition - main case" $ do
        let expect = OrPattern.fromPatterns []
        actual <-
            evaluate
                Conditional
                    { term =
                        -- Use the exact form we expect from an owise condition
                        -- for f(constr10(x)) = something
                        --     f(x) = something-else [owise]
                        mkAnd
                            (mkNot
                                (mkOr
                                    (mkExists Mock.xConfig
                                        (mkAnd
                                            mkTop_
                                            (mkAnd
                                                (mkCeil_
                                                    (mkAnd
                                                        (Mock.constr10
                                                            (mkElemVar
                                                                Mock.xConfig
                                                            )
                                                        )
                                                        (Mock.constr10 Mock.a)
                                                    )
                                                )
                                                mkTop_
                                            )
                                        )
                                    )
                                    mkBottom_
                                )
                            )
                            mkTop_
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        assertEqual "" expect actual

    , testCase "owise condition - owise case" $ do
        let expect = OrPattern.fromPatterns [Pattern.top]
        actual <-
            evaluate
                Conditional
                    { term =
                        -- Use the exact form we expect from an owise condition
                        -- for f(constr10(x)) = something
                        --     f(x) = something-else [owise]
                        mkAnd
                            (mkNot
                                (mkOr
                                    (mkExists Mock.xConfig
                                        (mkAnd
                                            mkTop_
                                            (mkAnd
                                                (mkCeil_
                                                    (mkAnd
                                                        (Mock.constr10
                                                            (mkElemVar
                                                                Mock.xConfig
                                                            )
                                                        )
                                                        (Mock.constr11 Mock.a)
                                                    )
                                                )
                                                mkTop_
                                            )
                                        )
                                    )
                                    mkBottom_
                                )
                            )
                            mkTop_
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        assertEqual "" expect actual

     , testCase "map-like simplification" $ do
        let expect =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = mkTop_
                        , predicate = makeAndPredicate
                            (makeAndPredicate
                                (makeCeilPredicate Mock.cf)
                                (makeCeilPredicate (Mock.plain10 Mock.cf))
                            )
                            (makeAndPredicate
                                (makeCeilPredicate
                                    (mkAnd
                                        (Mock.plain10 Mock.cf)
                                        (Mock.plain10 (mkElemVar Mock.xConfig))
                                    )
                                )
                                (makeCeilPredicate
                                    (Mock.plain10 (mkElemVar Mock.xConfig))
                                )
                            )
                        , substitution = Substitution.unsafeWrap
                            [(inject Mock.yConfig, Mock.b)]
                        }
                    ]
        actual <-
            evaluate
                Conditional
                    { term = mkCeil_
                        (mkAnd
                            (Mock.constr20
                                (Mock.plain10 Mock.cf)
                                Mock.b
                            )
                            (Mock.constr20
                                (Mock.plain10 (mkElemVar Mock.xConfig))
                                (mkElemVar Mock.yConfig)
                            )
                        )
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        assertEqual "" expect actual
    , testCase "map function, non-matching" $ do
        let
            initial =
                Pattern.fromTermLike
                $ Mock.function20MapTest (Mock.builtinMap []) Mock.a
            expect = OrPattern.fromPattern initial
        actual <-
            evaluateWithAxioms
                (mkEvaluatorRegistry
                    (Map.fromList
                        [   ( AxiomIdentifier.Application
                                Mock.function20MapTestId
                            ,   [ mkEquation
                                    (Mock.function20MapTest
                                        (Mock.concatMap
                                            (Mock.elementMap
                                                (mkElemVar Mock.x)
                                                (mkElemVar Mock.y)
                                            )
                                            (mkElemVar Mock.m)
                                        )
                                        (mkElemVar Mock.x)
                                    )
                                    (mkElemVar Mock.y)
                                    & Equation.mapVariables
                                        (pure mkRuleVariable)
                                ]
                            )
                        ]
                    )
                )
                initial
        assertEqual "" expect actual
    , testCase "function application with top predicate" $ do
        let requirement =
                makeEqualsPredicate
                    (Mock.f (mkElemVar Mock.xRule))
                    (Mock.g Mock.b)
            expect =
                OrPattern.fromTermLike
                $ Mock.functionalConstr11 $ Mock.g Mock.a
        actual <-
            evaluateConditionalWithAxioms
                ( mkEvaluatorRegistry
                    ( Map.fromList
                        [ (AxiomIdentifier.Application Mock.functionalConstr10Id
                          , [ axiom
                                (Mock.functionalConstr10 (mkElemVar Mock.xRule))
                                (Mock.g Mock.a)
                                requirement
                            ]
                          )
                        ]
                    )
                )
                (from @(Predicate _) @(SideCondition _) requirement)
                (Pattern.fromTermLike
                    $ mkExists Mock.zRule
                    $ Mock.functionalConstr11
                    $ Mock.functionalConstr10 (mkElemVar Mock.xRule)
                )
        assertEqual "" expect actual
    , testCase "no function branching" $ do
        let expect =
                OrPattern.fromPatterns
                [ Conditional
                    { term = Mock.functional10 (mkElemVar Mock.xConfig)
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                ]
        actual <-
            evaluateWithAxioms
                ( mkEvaluatorRegistry
                    ( Map.fromList
                        [   (AxiomIdentifier.Application Mock.functional10Id
                            ,   [ conditionalEqualityPattern
                                    (Mock.functional10 (mkElemVar Mock.x))
                                    (makeEqualsPredicate Mock.cf Mock.a)
                                    (mkElemVar Mock.x)
                                    & Equation.mapVariables
                                        (pure mkRuleVariable)
                                , conditionalEqualityPattern
                                    (Mock.functional10 (mkElemVar Mock.x))
                                    (makeNotPredicate
                                        (makeEqualsPredicate Mock.cf Mock.a)
                                    )
                                    (mkElemVar Mock.x)
                                    & Equation.mapVariables
                                        (pure mkRuleVariable)
                                ]
                            )
                       ]
                    )
                )
                Conditional
                    { term = Mock.functional10 (mkElemVar Mock.xConfig)
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        assertEqual "" expect actual

    , testCase "exists variable equality" $ do
        let
            expect = OrPattern.top
        actual <-
            evaluateWithAxioms
                Map.empty
                Conditional
                    { term =
                        mkExists
                            Mock.xConfig
                            (mkEquals_
                                (mkElemVar Mock.xConfig)
                                (mkElemVar Mock.yConfig)
                            )
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        assertEqual "" expect actual
    , testCase "exists variable equality reverse" $ do
        let
            expect = OrPattern.top
        actual <-
            evaluateWithAxioms
                Map.empty
                Conditional
                    { term =
                        mkExists
                            Mock.xConfig
                            (mkEquals_
                                (mkElemVar Mock.yConfig)
                                (mkElemVar Mock.xConfig)
                            )
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        assertEqual "" expect actual
    , testCase "exists variable equality" $ do
        actual <-
            evaluateWithAxioms Map.empty
            $ Pattern.fromTermLike
            $ mkExists Mock.xConfig
            $ mkEquals_ (mkElemVar Mock.xConfig) (mkElemVar Mock.yConfig)
        assertEqual "" OrPattern.top actual
    , testCase "exists variable equality reverse" $ do
        actual <-
            evaluateWithAxioms Map.empty
            $ Pattern.fromTermLike
            $ mkExists Mock.xConfig
            $ mkEquals_ (mkElemVar Mock.yConfig) (mkElemVar Mock.xConfig)
        assertEqual "" OrPattern.top actual

    , testCase "simplification with top predicate (exists variable capture)"
      $ do
        let requirement =
                makeEqualsPredicate
                    (Mock.f (mkElemVar Mock.xRule))
                    (Mock.g Mock.b)
            expect =
                OrPattern.fromPatterns
                [ Conditional
                    { term =
                            mkExists
                                Mock.var_xRule_0
                                (mkElemVar Mock.var_xRule_0)
                    , predicate = requirement
                    , substitution = mempty
                    }
                ]
        actual <-
            evaluateWithAxioms
                ( mkEvaluatorRegistry
                    ( Map.fromList
                        [ (AxiomIdentifier.Application Mock.functionalConstr10Id
                          , [ axiom
                                (Mock.functionalConstr10 (mkElemVar Mock.xRule))
                                (Mock.g Mock.a)
                                requirement
                            ]
                          )
                        ]
                    )
                )
                Conditional
                    { term = mkExists Mock.xRule (mkElemVar Mock.xRule)
                    , predicate = requirement
                    , substitution = mempty
                    }
        assertEqual "" expect actual
    , testCase "simplification with top predicate (forall variable capture)"
      $ do
        let requirement =
                makeEqualsPredicate
                    (Mock.f (mkElemVar Mock.xRule))
                    (Mock.g Mock.b)
            expect =
                OrPattern.fromPatterns
                [ Conditional
                    { term =
                        mkForall
                            Mock.var_xRule_0
                            (mkElemVar Mock.var_xRule_0)
                    , predicate = requirement
                    , substitution = mempty
                    }
                ]
        actual <-
            evaluateWithAxioms
                ( mkEvaluatorRegistry
                    ( Map.fromList
                        [ (AxiomIdentifier.Application Mock.functionalConstr10Id
                          , [ axiom
                                (Mock.functionalConstr10 (mkElemVar Mock.xRule))
                                (Mock.g Mock.a)
                                requirement
                            ]
                          )
                        ]
                    )
                )
                Conditional
                    { term = mkForall Mock.xRule (mkElemVar Mock.xRule)
                    , predicate = requirement
                    , substitution = mempty
                    }
        assertEqual "" expect actual
    , testCase "simplification with top predicate (nu variable capture)" $ do
        let requirement =
                makeEqualsPredicate
                    (Mock.f (mkSetVar Mock.setXRule))
                    (Mock.g Mock.b)
            expect =
                OrPattern.fromPatterns
                [ Conditional
                    { term =
                        mkNu
                            Mock.var_setXRule_0
                            (mkSetVar Mock.var_setXRule_0)
                    , predicate = requirement
                    , substitution = mempty
                    }
                ]
        actual <-
            evaluateWithAxioms
                ( mkEvaluatorRegistry
                    ( Map.fromList
                        [ (AxiomIdentifier.Application Mock.functionalConstr10Id
                          , [ axiom
                                (Mock.functionalConstr10 (mkElemVar Mock.xRule))
                                (Mock.g Mock.a)
                                requirement
                            ]
                          )
                        ]
                    )
                )
                Conditional
                    { term = mkNu Mock.setXRule (mkSetVar Mock.setXRule)
                    , predicate = requirement
                    , substitution = mempty
                    }
        assertEqual "" expect actual
    , testCase "simplification with top predicate (mu variable capture)" $ do
        let requirement =
                makeEqualsPredicate
                    (Mock.f (mkSetVar Mock.setXRule))
                    (Mock.g Mock.b)
            expect =
                OrPattern.fromPatterns
                [ Conditional
                    { term =
                        mkMu
                            Mock.var_setXRule_0
                            (mkSetVar Mock.var_setXRule_0)
                    , predicate = requirement
                    , substitution = mempty
                    }
                ]
        actual <-
            evaluateWithAxioms
                ( mkEvaluatorRegistry
                    ( Map.fromList
                        [ (AxiomIdentifier.Application Mock.functionalConstr10Id
                          , [ axiom
                                (Mock.functionalConstr10 (mkElemVar Mock.xRule))
                                (Mock.g Mock.a)
                                requirement
                            ]
                          )
                        ]
                    )
                )
                Conditional
                    { term = mkMu Mock.setXRule (mkSetVar Mock.setXRule)
                    , predicate = requirement
                    , substitution = mempty
                    }
        assertEqual "" expect actual
    , testCase "Iff simplification" $ do
        let expected = OrPattern.fromPatterns
                [Conditional
                    { term = mkNot Mock.bSort0
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                ]
        actual <- evaluate
            Conditional
                { term = mkIff Mock.bSort0 mkBottom_
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertEqual "" expected actual
    , testCase "Rewrite simplification" $ do
        let expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkRewrites (mkElemVar Mock.xConfig) mkBottom_
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                ]
        actual <- evaluate
            Conditional
                { term = mkRewrites (mkElemVar Mock.xConfig) mkBottom_
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertEqual "" expected actual
    , testCase "Or to pattern" $ do
        let expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop Mock.boolSort
                    , predicate = makeIffPredicate
                        (makeOrPredicate
                            (makeAndPredicate
                                (makeCeilPredicate Mock.cf)
                                (makeCeilPredicate Mock.cg)
                            )
                            (makeCeilPredicate Mock.cf)
                        )
                        (makeCeilPredicate Mock.ch)
                    , substitution = mempty
                    }
                ]
        actual <- evaluate
            Conditional
                { term = mkIff
                    (mkIn Mock.boolSort
                        (mkCeil_ Mock.cf)
                        (mkOr
                            Mock.unitSet
                            (mkCeil_ Mock.cg)
                        )
                    )
                    (mkCeil_ Mock.ch)
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertEqual "" expected actual
    , testCase "Sort matching" $ do
        let mx =
                Variable
                { variableName =
                    SetVariableName
                    $ mkConfigVariable
                        VariableName
                        { base = testId "mx"
                        , counter = mempty
                        }
                , variableSort = Mock.subOthersort
                }
            iz =
                Variable
                { variableName =
                    SetVariableName
                    $ mkConfigVariable
                        VariableName
                        { base = testId "iz"
                        , counter = mempty
                        }
                , variableSort = Mock.intSort
                }
            ub =
                Variable
                { variableName =
                    ElementVariableName
                    $ mkConfigVariable
                        VariableName
                        { base = testId "ub"
                        , counter = mempty
                        }
                , variableSort = Mock.boolSort
                }

        let expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop Mock.otherSort
                    , predicate =
                        makeAndPredicate
                            (makeAndPredicate
                                (makeCeilPredicate
                                    (mkAnd
                                        (Mock.tdivInt mkTop_ mkTop_)
                                        (mkNu iz (Mock.builtinInt 595))
                                    )
                                )
                                (makeAndPredicate
                                    (makeCeilPredicate
                                        (Mock.tdivInt mkTop_ mkTop_)
                                    )
                                    (makeCeilPredicate
                                        (mkNu iz (Mock.builtinInt 595))
                                    )
                                )
                            )
                            (makeAndPredicate
                                (makeCeilPredicate
                                    (mkNot
                                        (mkNu mx
                                            (mkRewrites
                                                mkBottom_
                                                Mock.aSubOthersort
                                            )
                                        )
                                    )
                                )
                                (makeEqualsPredicate
                                    Mock.functionalInjective00
                                    (Mock.g
                                        (Mock.functionalConstr30
                                            (Mock.functionalTopConstr21
                                                Mock.ch
                                                Mock.aTopSort
                                            )
                                            (mkIff Mock.plain00 Mock.d)
                                            Mock.cg
                                        )
                                    )
                                )
                            )
                    , substitution = mempty
                    }
                , Conditional
                    { term = mkTop Mock.otherSort
                    , predicate =
                        makeAndPredicate
                            (makeAndPredicate
                                (makeCeilPredicate
                                    (mkAnd
                                        (Mock.tdivInt mkTop_ mkTop_)
                                        (mkNu iz (Mock.builtinInt 595))
                                    )
                                )
                                (makeAndPredicate
                                    (makeCeilPredicate
                                        (Mock.tdivInt mkTop_ mkTop_)
                                    )
                                    (makeCeilPredicate
                                        (mkNu iz (Mock.builtinInt 595))
                                    )
                                )
                            )
                            (makeAndPredicate
                                (makeEqualsPredicate
                                    Mock.functionalInjective00
                                    (Mock.g
                                        (Mock.functionalConstr30
                                            (Mock.functionalTopConstr21
                                                Mock.ch
                                                Mock.aTopSort
                                            )
                                            (mkIff Mock.plain00 Mock.d)
                                            Mock.cg
                                        )
                                    )
                                )
                                (makeNotPredicate
                                    (makeFloorPredicate (Mock.builtinList []))
                                )
                            )
                    , substitution = mempty
                    }
                ]
        actual <- evaluate
            Conditional
                { term = mkIn Mock.otherSort
                    (mkNu iz (Mock.builtinInt 595))
                    (Mock.tdivInt
                        (mkForall ub
                            (mkCeil Mock.intSort
                                (mkNot
                                    (mkAnd
                                        (mkFloor Mock.subOthersort
                                            Mock.unitList
                                        )
                                        (mkNu mx
                                            (mkRewrites
                                                (mkBottom Mock.subOthersort)
                                                Mock.aSubOthersort
                                            )
                                        )
                                    )
                                )
                            )
                        )
                        (mkAnd
                            (mkTop Mock.intSort)
                            (mkEquals Mock.intSort
                                (Mock.g
                                    (Mock.functionalConstr30
                                        (Mock.functionalTopConstr21
                                            Mock.ch
                                            Mock.aTopSort
                                        )
                                        (mkIff Mock.plain00 Mock.d)
                                        Mock.cg
                                    )
                                )
                                Mock.functionalInjective00
                            )
                        )
                    )
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertEqual "" expected actual
    , testCase "Builtin and simplification failure" $ do
        let m =
                mkSetVariable (testId "m") Mock.listSort
                & mapSetVariable (pure mkConfigVariable)
            ue =
                mkSetVariable (testId "ue") Mock.listSort
                & mapSetVariable (pure mkConfigVariable)
        actual <- evaluate
            Conditional
                { term = mkAnd
                    (Mock.concatList
                        (mkImplies
                            (mkImplies mkBottom_ mkTop_)
                            (mkIn_ Mock.cfSort0 Mock.cgSort0)
                        )
                        (mkImplies
                            (mkAnd
                                (mkMu m mkBottom_)
                                mkBottom_
                            )
                            (mkImplies Mock.unitList (mkNu ue Mock.unitList))
                        )
                    )
                    Mock.unitList
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertBool
            "Expecting simplification"
            (OrPattern.isSimplified sideRepresentation actual)
    , testCase "Forall simplification" $ do
        let expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop Mock.otherSort
                    , predicate =
                        makeCeilPredicate
                            (mkEvaluated (mkBottom Mock.mapSort))
                    , substitution = mempty
                    }
                ]
        actual <- evaluate
            Conditional
                { term = mkForall
                    Mock.tConfig
                    (mkIn
                        Mock.otherSort
                        (mkNot (mkBottom Mock.mapSort))
                        (mkEvaluated mkBottom_)
                    )
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertEqual "" expected actual
    , testCase "Implies simplification" $ do
        let zz =
                mkElementVariable (testId "zz") Mock.subOthersort
                & mapElementVariable (pure mkConfigVariable)
            mci =
                mkElementVariable (testId "mci") Mock.subOthersort
                & mapElementVariable (pure mkConfigVariable)
            mw =
                mkElementVariable (testId "mw") Mock.subOthersort
                & mapElementVariable (pure mkConfigVariable)
            k =
                mkSetVariable (testId "k") Mock.setSort
                & mapSetVariable (pure mkConfigVariable)

        let expects =
                [ Conditional
                    { term = mkTop Mock.stringSort
                    , predicate = makeAndPredicate
                        (makeImpliesPredicate
                            (makeAndPredicate
                                (makeCeilPredicate
                                    (mkAnd
                                        (Mock.fSet mkTop_)
                                        (mkMu k
                                            (asInternal (Set.fromList [Mock.a]))
                                        )
                                    )
                                )
                                (makeAndPredicate
                                    (makeCeilPredicate
                                        (Mock.fSet mkTop_)
                                    )
                                    (makeCeilPredicate
                                        (mkMu k
                                            (asInternal (Set.fromList [Mock.a]))
                                        )
                                    )
                                )
                            )
                            (makeIffPredicate
                                (makeEqualsPredicate Mock.aSubSubsort mkTop_)
                                (makeFloorPredicate
                                    (mkEvaluated (mkBottom Mock.testSort))
                                )
                            )
                        )
                        (makeImpliesPredicate
                            (makeAndPredicate
                                (makeCeilPredicate
                                    (mkAnd
                                        (Mock.fSet mkTop_)
                                        (mkMu k
                                            (mkEvaluated Mock.unitSet)
                                        )
                                    )
                                )
                                (makeAndPredicate
                                    (makeCeilPredicate
                                        (Mock.fSet mkTop_)
                                    )
                                    (makeCeilPredicate
                                        (mkMu k
                                            (mkEvaluated Mock.unitSet)
                                        )
                                    )
                                )
                            )
                            (makeIffPredicate
                                (makeEqualsPredicate Mock.aSubSubsort mkTop_)
                                (makeFloorPredicate
                                    (mkEvaluated (mkBottom Mock.testSort))
                                )
                            )
                        )
                    , substitution = mempty
                    }
                ]
        actuals <- evaluate
            Conditional
                { term = mkImplies
                    (mkCeil_
                        (mkIn Mock.testSort0
                            (mkMu k
                                (mkOr
                                    (mkEvaluated Mock.unitSet)
                                    (mkExists mw (Mock.elementSet Mock.a))
                                )
                            )
                            (Mock.fSet (mkFloor_ (mkTop Mock.mapSort)))
                        )
                    )
                    (mkEquals Mock.stringSort
                        (mkFloor Mock.testSort0
                            (mkEvaluated (mkBottom Mock.testSort))
                        )
                        (mkFloor Mock.testSort0
                            (mkExists mci
                                (mkCeil Mock.setSort
                                    (mkForall
                                        zz
                                        (mkEquals_ Mock.aSubSubsort mkTop_)
                                    )
                                )
                            )
                        )
                    )

                , predicate = makeTruePredicate
                , substitution = mempty
                }
        for_ (align expects (Foldable.toList actuals)) $ \these -> do
            (expect, actual) <- expectThese these
            on (assertEqual "") term expect actual
            on (assertEqual "") (MultiAnd.fromPredicate . predicate) expect actual
            on (assertEqual "") substitution expect actual
    , testCase "Ceil simplification" $ do
        actual <- evaluate
            Conditional
                { term = mkCeil Mock.topSort
                    (mkForall Mock.xConfig
                        (Mock.concatSet
                            (mkEvaluated (mkEvaluated (mkTop Mock.setSort)))
                            (mkEvaluated (mkEvaluated (mkTop Mock.setSort)))
                        )
                    )
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertBool "Expecting simplification"
            (OrPattern.isSimplified sideRepresentation actual)
    , testCase "Equals-in simplification" $ do
        let gt =
                mkSetVariable (testId "gt") Mock.stringSort
                & mapSetVariable (pure mkConfigVariable)
            g =
                mkSetVariable (testId "g") Mock.testSort1
                & mapSetVariable (pure mkConfigVariable)
        actual <- evaluate
            Conditional
                { term = mkNu gt
                    (mkEquals_
                        (mkIn_
                            mkTop_
                            (mkNu g (mkOr Mock.aSort1 (mkSetVar g)))
                        )
                        mkTop_
                    )
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertBool "" (OrPattern.isSimplified sideRepresentation actual)
    , testCase "And-list simplification" $ do
        actual <- evaluate
            Conditional
                { term = mkAnd
                    (Mock.elementList Mock.plain00)
                    (Mock.elementList Mock.functional00)
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertBool "" (OrPattern.isSimplified sideRepresentation actual)
    , testCase "Distributed equals simplification" $ do
        let k =
                mkSetVariable (testId "k") Mock.stringSort
                & mapSetVariable (pure mkConfigVariable)
        actual <- evaluate
            Conditional
                { term = mkMu k
                    (mkEquals_
                        (Mock.functionalConstr21 Mock.cf Mock.cf)
                        (Mock.functionalConstr21 Mock.ch Mock.cg)
                    )
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertBool "" (OrPattern.isSimplified sideRepresentation actual)
    , testCase "nu-floor-in-or simplification" $ do
        let q =
                mkSetVariable (testId "q") Mock.otherSort
                & mapSetVariable (pure mkConfigVariable)
        actual <- evaluate
            Conditional
                { term = mkNu q
                    (mkFloor_
                        (mkIn_
                            (Mock.g Mock.ch)
                            (mkOr Mock.cf Mock.cg)
                        )
                    )
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertBool "" (OrPattern.isSimplified sideRepresentation actual)
    , testCase "equals-predicate with sort change simplification" $ do
        actual <- evaluate
            Conditional
                { term =
                    mkEquals Mock.testSort
                        (mkIn Mock.subSort
                            (mkStringLiteral "a")
                            (mkStringLiteral "b")
                        )
                        mkBottom_
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertBool "" (OrPattern.isSimplified sideRepresentation actual)
    , testCase "Preserves predicate sort" $ do
        let patt = Conditional
                { term = mkTop Mock.listSort
                , predicate = makeInPredicate Mock.cf Mock.cg
                , substitution = mempty
                }
            expected = Conditional
                { term = mkTop Mock.listSort
                , predicate =
                    makeAndPredicate
                        (makeCeilPredicate Mock.cf)
                        (makeEqualsPredicate Mock.cf Mock.cg)
                , substitution = mempty
                }
        actual <- evaluate patt
        assertEqual "" (OrPattern.fromPattern expected) actual
    , testCase "Not-iff-evaluated simplification" $ do
        let patt = Conditional
                { term =
                    mkNot
                        (mkIff
                            mkBottom_
                            (mkEvaluated Mock.unitMap)
                        )
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            expected = OrPattern.fromPattern Conditional
                { term = mkEvaluated Mock.unitMap
                , predicate = makeTruePredicate
                , substitution = mempty
                }

        actual <- evaluate patt
        assertEqual "" expected actual
    , testCase "Defined is kept after simplification" $ do
        let patt =
                mkOr
                    (Mock.f (mkElemVar Mock.xConfig))
                    (Mock.g Mock.a)
                & mkDefined
                & Pattern.fromTermLike
            expected =
                OrPattern.fromPatterns
                [ mkElemVar Mock.xConfig
                    & Pattern.fromTermLike
                , defined (Mock.g Mock.a)
                    & Pattern.fromTermLike
                ]
        actual <-
            evaluateWithAxioms
                ( mkEvaluatorRegistry
                    ( Map.fromList
                        [ (AxiomIdentifier.Application Mock.fId
                          , [ axiom
                                (Mock.f (mkElemVar Mock.xRule))
                                (mkElemVar Mock.xRule)
                                makeTruePredicate
                            ]
                          )
                        ]
                    )
                )
                patt
        assertEqual "" expected actual
    ]
  where
    defined = mkDefinedAtTop

test_simplificationIntegrationUnification :: [TestTree]
test_simplificationIntegrationUnification =
    [ testCase "map function, non-matching" $ do
        let
            initial =
                Pattern.fromTermLike
                $ Mock.function20MapTest (Mock.builtinMap []) Mock.a
            expect = OrPattern.fromPattern initial
        actual <-
            evaluateWithAxioms
                (mkEvaluatorRegistry
                    (Map.fromList
                        [   ( AxiomIdentifier.Application
                                Mock.function20MapTestId
                            ,   [ functionAxiomUnification_
                                    Mock.function20MapTestSymbol
                                    [Mock.concatMap
                                        (Mock.elementMap
                                            (mkElemVar Mock.xRule)
                                            (mkElemVar Mock.yRule)
                                        )
                                        (mkElemVar Mock.mRule)
                                    , mkElemVar Mock.xRule
                                    ]
                                    (mkElemVar Mock.yRule)
                                ]
                            )
                        ]
                    )
                )
                initial
        assertEqual "" expect actual
    , testCase "function application with top predicate" $ do
        let requirement =
                makeEqualsPredicate
                    (Mock.f (mkElemVar Mock.xRule))
                    (Mock.g Mock.b)
            expect =
                OrPattern.fromTermLike
                $ Mock.functionalConstr11 $ Mock.g Mock.a
        actual <-
            evaluateConditionalWithAxioms
                ( mkEvaluatorRegistry
                    ( Map.fromList
                        [ (AxiomIdentifier.Application Mock.functionalConstr10Id
                          , [ functionAxiomUnification
                                Mock.functionalConstr10Symbol
                                [mkElemVar Mock.xRule]
                                (Mock.g Mock.a)
                                requirement
                            ]
                          )
                        ]
                    )
                )
                (from @(Predicate _) @(SideCondition _) requirement)
                (Pattern.fromTermLike
                    $ mkExists Mock.zRule
                    $ Mock.functionalConstr11
                    $ Mock.functionalConstr10 (mkElemVar Mock.xRule)
                )
        assertEqual "" expect actual
    , testCase "no function branching" $ do
        let expect =
                OrPattern.fromPatterns
                [ Conditional
                    { term = Mock.functional10 (mkElemVar Mock.xConfig)
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                ]
        actual <-
            evaluateWithAxioms
                ( mkEvaluatorRegistry
                    ( Map.fromList
                        [   (AxiomIdentifier.Application Mock.functional10Id
                            ,   [ functionAxiomUnification
                                    Mock.functional10Symbol
                                    [mkElemVar Mock.xRule]
                                    (mkElemVar Mock.xRule)
                                    (makeEqualsPredicate Mock.cf Mock.a)
                                , functionAxiomUnification
                                    Mock.functional10Symbol
                                    [mkElemVar Mock.xRule]
                                    (mkElemVar Mock.xRule)
                                    (makeNotPredicate
                                        (makeEqualsPredicate Mock.cf Mock.a)
                                    )
                                ]
                            )
                       ]
                    )
                )
                Conditional
                    { term = Mock.functional10 (mkElemVar Mock.xConfig)
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        assertEqual "" expect actual

    , testCase "simplification with top predicate (exists variable capture)"
      $ do
        let requirement =
                makeEqualsPredicate
                    (Mock.f (mkElemVar Mock.xRule))
                    (Mock.g Mock.b)
            expect =
                OrPattern.fromPatterns
                [ Conditional
                    { term =
                        mkExists
                            Mock.var_xRule_0
                            (mkElemVar Mock.var_xRule_0)
                    , predicate = requirement
                    , substitution = mempty
                    }
                ]
        actual <-
            evaluateWithAxioms
                ( mkEvaluatorRegistry
                    ( Map.fromList
                        [ (AxiomIdentifier.Application Mock.functionalConstr10Id
                          , [ functionAxiomUnification
                                Mock.functionalConstr10Symbol
                                [mkElemVar Mock.xRule]
                                (Mock.g Mock.a)
                                requirement
                            ]
                          )
                        ]
                    )
                )
                Conditional
                    { term = mkExists Mock.xRule (mkElemVar Mock.xRule)
                    , predicate = requirement
                    , substitution = mempty
                    }
        assertEqual "" expect actual
    , testCase "simplification with top predicate (forall variable capture)"
      $ do
        let requirement =
                makeEqualsPredicate
                    (Mock.f (mkElemVar Mock.xRule))
                    (Mock.g Mock.b)
            expect =
                OrPattern.fromPatterns
                [ Conditional
                    { term =
                        mkForall
                            Mock.var_xRule_0
                            (mkElemVar Mock.var_xRule_0)
                    , predicate = requirement
                    , substitution = mempty
                    }
                ]
        actual <-
            evaluateWithAxioms
                ( mkEvaluatorRegistry
                    ( Map.fromList
                        [ (AxiomIdentifier.Application Mock.functionalConstr10Id
                          , [ functionAxiomUnification
                                Mock.functionalConstr10Symbol
                                [mkElemVar Mock.xRule]
                                (Mock.g Mock.a)
                                requirement
                            ]
                          )
                        ]
                    )
                )
                Conditional
                    { term = mkForall Mock.xRule (mkElemVar Mock.xRule)
                    , predicate = requirement
                    , substitution = mempty
                    }
        assertEqual "" expect actual
    , testCase "simplification with top predicate (nu variable capture)" $ do
        let requirement =
                makeEqualsPredicate
                    (Mock.f (mkSetVar Mock.setXRule))
                    (Mock.g Mock.b)
            expect =
                OrPattern.fromPatterns
                [ Conditional
                    { term =
                        mkNu
                            Mock.var_setXRule_0
                            (mkSetVar Mock.var_setXRule_0)
                    , predicate = requirement
                    , substitution = mempty
                    }
                ]
        actual <-
            evaluateWithAxioms
                ( mkEvaluatorRegistry
                    ( Map.fromList
                        [ (AxiomIdentifier.Application Mock.functionalConstr10Id
                          , [ functionAxiomUnification
                                Mock.functionalConstr10Symbol
                                [mkElemVar Mock.xRule]
                                (Mock.g Mock.a)
                                requirement
                            ]
                          )
                        ]
                    )
                )
                Conditional
                    { term = mkNu Mock.setXRule (mkSetVar Mock.setXRule)
                    , predicate = requirement
                    , substitution = mempty
                    }
        assertEqual "" expect actual
    , testCase "simplification with top predicate (mu variable capture)" $ do
        let requirement =
                makeEqualsPredicate
                    (Mock.f (mkSetVar Mock.setXRule))
                    (Mock.g Mock.b)
            expect =
                OrPattern.fromPatterns
                [ Conditional
                    { term =
                        mkMu
                            Mock.var_setXRule_0
                            (mkSetVar Mock.var_setXRule_0)
                    , predicate = requirement
                    , substitution = mempty
                    }
                ]
        actual <-
            evaluateWithAxioms
                ( mkEvaluatorRegistry
                    ( Map.fromList
                        [ (AxiomIdentifier.Application Mock.functionalConstr10Id
                          , [ functionAxiomUnification
                                Mock.functionalConstr10Symbol
                                [mkElemVar Mock.xRule]
                                (Mock.g Mock.a)
                                requirement
                            ]
                          )
                        ]
                    )
                )
                Conditional
                    { term = mkMu Mock.setXRule (mkSetVar Mock.setXRule)
                    , predicate = requirement
                    , substitution = mempty
                    }
        assertEqual "" expect actual
    ]

conditionalEqualityPattern
    :: InternalVariable variable
    => TermLike variable
    -> Predicate.Predicate variable
    -> TermLike variable
    -> Equation variable
conditionalEqualityPattern left requires right =
    mkEquation left right
    & Lens.set (field @"requires") requires


test_substitute :: [TestTree]
test_substitute =
    [ testCase "Substitution under unary functional constructor" $ do
        let expect =
                OrPattern.fromPatterns
                    [ Pattern.Conditional
                        { term =
                            Mock.functionalConstr20
                                Mock.a
                                (Mock.functionalConstr10 Mock.a)
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (inject Mock.xConfig, Mock.a)
                            ,   ( inject Mock.yConfig
                                , Mock.functionalConstr10 Mock.a
                                )
                            ]
                        }
                    ]
        actual <-
            evaluate
                (Pattern.fromTermLike
                    (mkAnd
                        (Mock.functionalConstr20
                            (mkElemVar Mock.xConfig)
                            (Mock.functionalConstr10 (mkElemVar Mock.xConfig))
                        )
                        (Mock.functionalConstr20 Mock.a (mkElemVar Mock.yConfig))
                    )
                )
        assertEqual
            "Expected substitution under unary functional constructor"
            expect
            actual

    , testCase "Substitution" $ do
        let expect =
                OrPattern.fromPatterns
                    [ Pattern.Conditional
                        { term =
                            Mock.functionalConstr20 Mock.a Mock.a
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (inject Mock.xConfig, Mock.a)
                            , (inject Mock.yConfig, Mock.a)
                            ]
                        }
                    ]
        actual <-
            evaluate
                (Pattern.fromTermLike
                    (mkAnd
                        (Mock.functionalConstr20
                            (mkElemVar Mock.xConfig)
                            (mkElemVar Mock.xConfig)
                        )
                        (Mock.functionalConstr20 Mock.a (mkElemVar Mock.yConfig))
                    )
                )
        assertEqual "Expected substitution" expect actual
    ]

test_substituteMap :: [TestTree]
test_substituteMap =
    [ testCase "Substitution applied to Map elements" $ do
        let testMapX =
                Mock.sortInjection Mock.testSort
                $ mkDomainBuiltinMap [(Mock.a, mkElemVar Mock.xConfig)]
            testMapA =
                Mock.sortInjection Mock.testSort
                $ mkDomainBuiltinMap [(Mock.a, Mock.a)]
            expect =
                OrPattern.fromPatterns
                    [ Pattern.Conditional
                        { term = Mock.functionalConstr20 Mock.a testMapA
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (inject Mock.xConfig, Mock.a)
                            , (inject Mock.yConfig, testMapA)
                            ]
                        }
                    ]
        actual <-
            (evaluate . Pattern.fromTermLike)
                (mkAnd
                    (Mock.functionalConstr20 (mkElemVar Mock.xConfig) testMapX)
                    (Mock.functionalConstr20 Mock.a (mkElemVar Mock.yConfig))
                )
        assertEqual
            "Expected substitution applied to Map elements"
            expect
            actual
    ]
  where
    mkDomainBuiltinMap = Mock.builtinMap

test_substituteList :: [TestTree]
test_substituteList =
    [ testCase "Substitution applied to List elements" $ do
        let testListX =
                Mock.sortInjection Mock.testSort
                $ mkDomainBuiltinList [Mock.a, mkElemVar Mock.xConfig]
            testListA =
                Mock.sortInjection Mock.testSort
                $ mkDomainBuiltinList [Mock.a, Mock.a]
            expect =
                OrPattern.fromPatterns
                    [ Pattern.Conditional
                        { term = Mock.functionalConstr20 Mock.a testListA
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (inject Mock.xConfig, Mock.a)
                            , (inject Mock.yConfig, testListA)
                            ]
                        }
                    ]
        actual <-
            (evaluate . Pattern.fromTermLike)
                (mkAnd
                    (Mock.functionalConstr20 (mkElemVar Mock.xConfig) testListX)
                    (Mock.functionalConstr20 Mock.a (mkElemVar Mock.yConfig))
                )
        assertEqual
            "Expected substitution applied to List elements"
            expect
            actual
    ]
  where
    mkDomainBuiltinList = Mock.builtinList

evaluate
    :: Pattern.Pattern RewritingVariableName
    -> IO (OrPattern.OrPattern RewritingVariableName)
evaluate = evaluateWithAxioms Map.empty

evaluateWithAxioms
    :: BuiltinAndAxiomSimplifierMap
    -> Pattern.Pattern RewritingVariableName
    -> IO (OrPattern.OrPattern RewritingVariableName)
evaluateWithAxioms axioms =
    evaluateConditionalWithAxioms axioms SideCondition.top

evaluateConditionalWithAxioms
    :: BuiltinAndAxiomSimplifierMap
    -> SideCondition'
    -> Pattern.Pattern RewritingVariableName
    -> IO (OrPattern.OrPattern RewritingVariableName)
evaluateConditionalWithAxioms axioms sideCondition =
    runSimplifierSMT env . Pattern.simplify sideCondition
  where
    env = Mock.env { simplifierAxioms }
    simplifierAxioms :: BuiltinAndAxiomSimplifierMap
    simplifierAxioms =
        Map.unionWith
            simplifierWithFallback
            builtinAxioms
            axioms

-- | A selection of builtin axioms used in the tests above.
builtinAxioms :: BuiltinAndAxiomSimplifierMap
builtinAxioms =
    Map.fromList
        [   ( AxiomIdentifier.Application Mock.concatMapId
            , Builtin.functionEvaluator Map.evalConcat
            )
        ,   ( AxiomIdentifier.Application Mock.elementMapId
            , Builtin.functionEvaluator Map.evalElement
            )
        ,   ( AxiomIdentifier.Application Mock.unitMapId
            , Builtin.functionEvaluator Map.evalUnit
            )
        ,   ( AxiomIdentifier.Application Mock.concatSetId
            , Builtin.functionEvaluator Set.evalConcat
            )
        ,   ( AxiomIdentifier.Application Mock.concatSetId
            , Builtin.functionEvaluator Set.evalConcat
            )
        ,   ( AxiomIdentifier.Application Mock.elementSetId
            , Builtin.functionEvaluator Set.evalElement
            )
        ,   ( AxiomIdentifier.Application Mock.unitSetId
            , Builtin.functionEvaluator Set.evalUnit
            )
        ,   ( AxiomIdentifier.Application Mock.concatListId
            , Builtin.functionEvaluator List.evalConcat
            )
        ,   ( AxiomIdentifier.Application Mock.elementListId
            , Builtin.functionEvaluator List.evalElement
            )
        ,   ( AxiomIdentifier.Application Mock.unitListId
            , Builtin.functionEvaluator List.evalUnit
            )
        ,   ( AxiomIdentifier.Application Mock.concatListId
            , Builtin.functionEvaluator List.evalConcat
            )
        ,   ( AxiomIdentifier.Application Mock.tdivIntId
            , builtinEvaluation (Int.builtinFunctions Map.! Int.tdivKey)
            )
        ]

axiom
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> Predicate variable
    -> Equation variable
axiom left right requires =
    Equation
        { left
        , requires
        , argument = Nothing
        , antiLeft = Nothing
        , right
        , ensures = Predicate.makeTruePredicate
        , attributes = Default.def
        }

-- | Specialize 'Set.builtinSet' to the builtin sort 'setSort'.
asInternal
    :: InternalVariable variable
    => Set.Set (TermLike Concrete)
    -> TermLike variable
asInternal =
    Ac.asInternalConcrete Mock.metadataTools Mock.setSort
    . Map.fromSet (const SetValue)
    . Set.map (retractKey >>> fromJust)

sideRepresentation :: SideCondition.Representation
sideRepresentation =
    SideCondition.toRepresentation (SideCondition.top :: SideCondition')
