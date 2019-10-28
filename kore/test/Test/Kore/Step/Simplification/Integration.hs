module Test.Kore.Step.Simplification.Integration
    ( test_simplificationIntegration
    , test_substituteMap
    , test_substituteList
    , test_substitute
    ) where

import qualified Control.Lens as Lens
import qualified Data.Default as Default
import Data.Function
    ( (&)
    )
import Data.Generics.Product
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Test.Tasty

import Kore.Attribute.Simplification
import qualified Kore.Builtin.AssociativeCommutative as Ac
import qualified Kore.Builtin.Int as Int
import qualified Kore.Builtin.List as List
import qualified Kore.Builtin.Map as Map
import qualified Kore.Builtin.Set as Set
import qualified Kore.Domain.Builtin as Domain
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Conditional (..)
    , Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
import Kore.Predicate.Predicate
    ( makeAndPredicate
    , makeCeilPredicate
    , makeEqualsPredicate
    , makeFloorPredicate
    , makeIffPredicate
    , makeImpliesPredicate
    , makeInPredicate
    , makeNotPredicate
    , makeOrPredicate
    , makeTruePredicate
    )
import qualified Kore.Predicate.Predicate as Predicate
import Kore.Step.Axiom.EvaluationStrategy
    ( builtinEvaluation
    , simplifierWithFallback
    )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
    ( AxiomIdentifier (..)
    )
import Kore.Step.Axiom.Registry
    ( axiomPatternsToEvaluators
    )
import Kore.Step.Rule
    ( EqualityRule (EqualityRule)
    , RulePattern (..)
    , rulePattern
    )
import qualified Kore.Step.Simplification.Pattern as Pattern
    ( simplify
    )
import Kore.Step.Simplification.Simplify
import qualified Kore.Unification.Substitution as Substitution
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import Test.Kore
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext

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
                                    (mkExists Mock.x
                                        (mkAnd
                                            mkTop_
                                            (mkAnd
                                                (mkCeil_
                                                    (mkAnd
                                                        (Mock.constr10
                                                            (mkElemVar Mock.x)
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
                                    (mkExists Mock.x
                                        (mkAnd
                                            mkTop_
                                            (mkAnd
                                                (mkCeil_
                                                    (mkAnd
                                                        (Mock.constr10
                                                            (mkElemVar Mock.x)
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
                        , predicate = makeCeilPredicate
                            (mkAnd
                                (Mock.plain10 Mock.cf)
                                (Mock.plain10 (mkElemVar Mock.x))
                            )
                        , substitution = Substitution.unsafeWrap
                            [(ElemVar Mock.y, Mock.b)]
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
                                (Mock.plain10 (mkElemVar Mock.x))
                                (mkElemVar Mock.y)
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
                (axiomPatternsToEvaluators
                    (Map.fromList
                        [   ( AxiomIdentifier.Application
                                Mock.function20MapTestId
                            ,   [ EqualityRule $ rulePattern
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
                                ]
                            )
                        ]
                    )
                )
                initial
        assertEqual "" expect actual
    , testCase "function application with top predicate" $ do
        let requirement =
                makeEqualsPredicate (Mock.f (mkElemVar Mock.x)) (Mock.g Mock.b)
            expect =
                OrPattern.fromPatterns
                [ Conditional
                    { term = Mock.functionalConstr11 $ Mock.g Mock.a
                    , predicate = requirement
                    , substitution = mempty
                    }
                ]
        actual <-
            evaluateWithAxioms
                ( axiomPatternsToEvaluators
                    ( Map.fromList
                        [ (AxiomIdentifier.Application Mock.functionalConstr10Id
                          , [ axiom
                                (Mock.functionalConstr10 (mkElemVar Mock.x))
                                (Mock.g Mock.a)
                                requirement
                            ]
                          )
                        ]
                    )
                )
                Conditional
                    { term =
                        mkExists
                            Mock.z
                            (Mock.functionalConstr11
                                (Mock.functionalConstr10 (mkElemVar Mock.x))
                            )
                    , predicate = requirement
                    , substitution = mempty
                    }
        assertEqual "" expect actual
    -- Checks that `f(x/x)` evaluates to `x/x and x != 0` when `f` is the
    -- identity function and `#ceil(x/y) => y != 0`
    , testCase "function application introduces definedness condition" $ do
        let testSortVariable = SortVariableSort $ SortVariable (testId "s")
            expect =
                OrPattern.fromPatterns
                [ Conditional
                    { term =
                        Mock.tdivInt
                            (mkElemVar Mock.xInt)
                            (mkElemVar Mock.xInt)
                    , predicate =
                        makeNotPredicate
                        $ makeEqualsPredicate
                            (mkElemVar Mock.xInt)
                            (Mock.builtinInt 0)
                    , substitution = mempty
                    }
                ]
        actual <-
            evaluateWithAxioms
                ( axiomPatternsToEvaluators
                    ( Map.fromList
                        [   (AxiomIdentifier.Application Mock.fIntId
                            ,   [ EqualityRule $ rulePattern
                                    (Mock.fInt (mkElemVar Mock.xInt))
                                    (mkElemVar Mock.xInt)
                                ]
                            )
                        ,   (AxiomIdentifier.Ceil
                                (AxiomIdentifier.Application Mock.tdivIntId)
                            ,   [ EqualityRule $ simplificationRulePattern
                                    (mkCeil testSortVariable
                                        $ Mock.tdivInt
                                            (mkElemVar Mock.xInt)
                                            (mkElemVar Mock.yInt)
                                    )
                                    (mkCeil testSortVariable
                                        . mkNot
                                        $ mkEquals testSortVariable
                                            (mkElemVar Mock.yInt)
                                            (Mock.builtinInt 0)

                                    )
                                ]
                            )
                        ]
                    )
                )
                Conditional
                    { term =
                        Mock.fInt
                        $ Mock.tdivInt
                            (mkElemVar Mock.xInt)
                            (mkElemVar Mock.xInt)
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
                            Mock.x
                            (mkEquals_ (mkElemVar Mock.x) (mkElemVar Mock.y))
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
                            Mock.x
                            (mkEquals_ (mkElemVar Mock.y) (mkElemVar Mock.x))
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        assertEqual "" expect actual
    , testCase "exists variable equality" $ do
        actual <-
            evaluateWithAxioms Map.empty
            $ Pattern.fromTermLike
            $ mkExists Mock.x
            $ mkEquals_ (mkElemVar Mock.x) (mkElemVar Mock.y)
        assertEqual "" OrPattern.top actual
    , testCase "exists variable equality reverse" $ do
        actual <-
            evaluateWithAxioms Map.empty
            $ Pattern.fromTermLike
            $ mkExists Mock.x
            $ mkEquals_ (mkElemVar Mock.y) (mkElemVar Mock.x)
        assertEqual "" OrPattern.top actual
    , testCase "new variable quantification" $ do
        let
            expect = OrPattern.fromPatterns
                [ Conditional
                    { term = mkExists Mock.x (Mock.f (mkElemVar Mock.x))
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                ]
        actual <-
            evaluateWithAxioms
                (axiomPatternsToEvaluators $ Map.fromList
                    [   ( AxiomIdentifier.Application Mock.cfId
                        ,   [ EqualityRule $ rulePattern
                                Mock.cf
                                (Mock.f (mkElemVar Mock.x))
                            ]
                        )
                    ]
                )
                Conditional
                    { term = Mock.cf
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        assertEqual "" expect actual
    , testCase "simplification with top predicate (exists variable capture)"
      $ do
        let requirement =
                makeEqualsPredicate (Mock.f (mkElemVar Mock.x)) (Mock.g Mock.b)
            expect =
                OrPattern.fromPatterns
                [ Conditional
                    { term = mkExists Mock.var_x_0 (mkElemVar Mock.var_x_0)
                    , predicate = requirement
                    , substitution = mempty
                    }
                ]
        actual <-
            evaluateWithAxioms
                ( axiomPatternsToEvaluators
                    ( Map.fromList
                        [ (AxiomIdentifier.Application Mock.functionalConstr10Id
                          , [ axiom
                                (Mock.functionalConstr10 (mkElemVar Mock.x))
                                (Mock.g Mock.a)
                                requirement
                            ]
                          )
                        ]
                    )
                )
                Conditional
                    { term = mkExists Mock.x (mkElemVar Mock.x)
                    , predicate = requirement
                    , substitution = mempty
                    }
        assertEqual "" expect actual
    , testCase "simplification with top predicate (forall variable capture)"
      $ do
        let requirement =
                makeEqualsPredicate (Mock.f (mkElemVar Mock.x)) (Mock.g Mock.b)
            expect =
                OrPattern.fromPatterns
                [ Conditional
                    { term = mkForall Mock.var_x_0 (mkElemVar Mock.var_x_0)
                    , predicate = requirement
                    , substitution = mempty
                    }
                ]
        actual <-
            evaluateWithAxioms
                ( axiomPatternsToEvaluators
                    ( Map.fromList
                        [ (AxiomIdentifier.Application Mock.functionalConstr10Id
                          , [ axiom
                                (Mock.functionalConstr10 (mkElemVar Mock.x))
                                (Mock.g Mock.a)
                                requirement
                            ]
                          )
                        ]
                    )
                )
                Conditional
                    { term = mkForall Mock.x (mkElemVar Mock.x)
                    , predicate = requirement
                    , substitution = mempty
                    }
        assertEqual "" expect actual
    , testCase "simplification with top predicate (nu variable capture)" $ do
        let requirement =
                makeEqualsPredicate (Mock.f (mkSetVar Mock.setX)) (Mock.g Mock.b)
            expect =
                OrPattern.fromPatterns
                [ Conditional
                    { term = mkNu Mock.var_setX_0 (mkSetVar Mock.var_setX_0)
                    , predicate = requirement
                    , substitution = mempty
                    }
                ]
        actual <-
            evaluateWithAxioms
                ( axiomPatternsToEvaluators
                    ( Map.fromList
                        [ (AxiomIdentifier.Application Mock.functionalConstr10Id
                          , [ axiom
                                (Mock.functionalConstr10 (mkElemVar Mock.x))
                                (Mock.g Mock.a)
                                requirement
                            ]
                          )
                        ]
                    )
                )
                Conditional
                    { term = mkNu Mock.setX (mkSetVar Mock.setX)
                    , predicate = requirement
                    , substitution = mempty
                    }
        assertEqual "" expect actual
    , testCase "simplification with top predicate (mu variable capture)" $ do
        let requirement =
                makeEqualsPredicate (Mock.f (mkSetVar Mock.setX)) (Mock.g Mock.b)
            expect =
                OrPattern.fromPatterns
                [ Conditional
                    { term = mkMu Mock.var_setX_0 (mkSetVar Mock.var_setX_0)
                    , predicate = requirement
                    , substitution = mempty
                    }
                ]
        actual <-
            evaluateWithAxioms
                ( axiomPatternsToEvaluators
                    ( Map.fromList
                        [ (AxiomIdentifier.Application Mock.functionalConstr10Id
                          , [ axiom
                                (Mock.functionalConstr10 (mkElemVar Mock.x))
                                (Mock.g Mock.a)
                                requirement
                            ]
                          )
                        ]
                    )
                )
                Conditional
                    { term = mkMu Mock.setX (mkSetVar Mock.setX)
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
                    { term = mkRewrites (mkElemVar Mock.x) mkBottom_
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                ]
        actual <- evaluate
            Conditional
                { term = mkRewrites (mkElemVar Mock.x) mkBottom_
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertEqual "" expected actual
    , testCase "Or to pattern" $ do
        let expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate = makeIffPredicate
                        (makeOrPredicate
                            (makeInPredicate
                                (mkCeil_ Mock.cf)
                                (mkCeil_ Mock.cg)
                            )
                            (makeInPredicate
                                (mkCeil_ Mock.cf)
                                (asInternal (Set.fromList []))
                            )
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
        let mx = SetVariable $ Variable (testId "mx") mempty Mock.subOthersort
            iz = SetVariable $ Variable (testId "iz") mempty Mock.intSort
            ub = ElementVariable $ Variable (testId "ub") mempty Mock.boolSort

        let expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate = makeInPredicate
                        (mkNu iz (Mock.builtinInt 595))
                        (mkAnd
                            (Mock.tdivInt mkTop_ mkTop_)
                            (mkAnd
                                (mkCeil_
                                    (mkNot
                                        (mkNu mx
                                            (mkRewrites
                                                mkBottom_
                                                Mock.aSubOthersort
                                            )
                                        )
                                    )
                                )
                                (mkEquals_
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
                    , substitution = mempty
                    }
                , Conditional
                    { term = mkTop_
                    , predicate = makeInPredicate
                        (mkNu iz (Mock.builtinInt 595))
                        (mkAnd
                            (Mock.tdivInt mkTop_ mkTop_)
                            (mkAnd
                                (mkEquals_
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
                                (mkNot (mkFloor_ (Mock.builtinList [])))
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
        let m = SetVariable $ Variable (testId "m") mempty Mock.listSort
            ue = SetVariable $ Variable (testId "ue") mempty Mock.listSort
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
        assertBool "Expecting simplification" (OrPattern.isSimplified actual)
    , testCase "Forall simplification" $ do
        let expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate =
                        makeCeilPredicate (mkEvaluated (mkBottom Mock.mapSort))
                    , substitution = mempty
                    }
                ]
        actual <- evaluate
            Conditional
                { term = mkForall
                    Mock.t
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
        let zz = ElementVariable
                $ Variable (testId "zz") mempty Mock.subOthersort
            mci = ElementVariable
                $ Variable (testId "mci") mempty Mock.subOthersort
            mw = ElementVariable
                $ Variable (testId "mw") mempty Mock.subOthersort
            k = SetVariable $ Variable (testId "k") mempty Mock.setSort

        let expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate = makeAndPredicate
                        (makeImpliesPredicate
                            (makeInPredicate
                                (mkMu k
                                    (asInternal (Set.fromList [Mock.ch]))
                                )
                                (Mock.fSet mkTop_)
                            )
                            (makeIffPredicate
                                (makeFloorPredicate
                                    (mkEvaluated (mkBottom Mock.testSort))
                                )
                                (makeEqualsPredicate Mock.aSubSubsort mkTop_)
                            )
                        )
                        (makeImpliesPredicate
                            (makeInPredicate
                                (mkMu k
                                    (mkEvaluated Mock.unitSet)
                                )
                                (Mock.fSet mkTop_)
                            )
                            (makeIffPredicate
                                (makeFloorPredicate
                                    (mkEvaluated (mkBottom Mock.testSort))
                                )
                                (makeEqualsPredicate Mock.aSubSubsort mkTop_)
                            )
                        )
                    , substitution = mempty
                    }
                ]
        actual <- evaluate
            Conditional
                { term = mkImplies
                    (mkCeil_
                        (mkIn Mock.testSort0
                            (mkMu k
                                (mkOr
                                    (mkEvaluated Mock.unitSet)
                                    (mkExists mw (Mock.elementSet Mock.ch))
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
        assertEqual "" expected actual
    , testCase "Ceil simplification" $ do
        actual <- evaluate
            Conditional
                { term = mkCeil Mock.topSort
                    (mkForall Mock.x
                        (Mock.concatSet
                            (mkEvaluated (mkEvaluated (mkTop Mock.setSort)))
                            (mkEvaluated (mkEvaluated (mkTop Mock.setSort)))
                        )
                    )
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertBool "Expecting simplification" (OrPattern.isSimplified actual)
    , testCase "Equals-in simplification" $ do
        let gt = SetVariable $ Variable (testId "gt") mempty Mock.stringSort
            g = SetVariable $ Variable (testId "g") mempty Mock.testSort1
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
        assertBool "" (OrPattern.isSimplified actual)
    , testCase "And-list simplification" $ do
        actual <- evaluate
            Conditional
                { term = mkAnd
                    (Mock.elementList Mock.plain00)
                    (Mock.elementList Mock.functional00)
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertBool "" (OrPattern.isSimplified actual)
    ]


simplificationRulePattern
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> RulePattern variable
simplificationRulePattern left right =
    patt & Lens.set (field @"attributes" . field @"simplification")
        (Simplification True)
  where
    patt = rulePattern left right

test_substitute :: [TestTree]
test_substitute =
    [ testCase "Substitution under unary functional constructor" $ do
        let expect =
                OrPattern.fromPatterns
                    [ Pattern.Conditional
                        { term =
                            Mock.functionalConstr20
                                Mock.a
                                (Mock.functionalConstr10 (mkElemVar Mock.x))
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (ElemVar Mock.x, Mock.a)
                            , (ElemVar Mock.y, Mock.functionalConstr10 Mock.a)
                            ]
                        }
                    ]
        actual <-
            evaluate
                (Pattern.fromTermLike
                    (mkAnd
                        (Mock.functionalConstr20
                            (mkElemVar Mock.x)
                            (Mock.functionalConstr10 (mkElemVar Mock.x))
                        )
                        (Mock.functionalConstr20 Mock.a (mkElemVar Mock.y))
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
                            Mock.functionalConstr20 Mock.a (mkElemVar Mock.y)
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (ElemVar Mock.x, Mock.a)
                            , (ElemVar Mock.y, Mock.a)
                            ]
                        }
                    ]
        actual <-
            evaluate
                (Pattern.fromTermLike
                    (mkAnd
                        (Mock.functionalConstr20
                            (mkElemVar Mock.x)
                            (mkElemVar Mock.x)
                        )
                        (Mock.functionalConstr20 Mock.a (mkElemVar Mock.y))
                    )
                )
        assertEqual "Expected substitution" expect actual
    ]

test_substituteMap :: [TestTree]
test_substituteMap =
    [ testCase "Substitution applied to Map elements" $ do
        let testMapX =
                Mock.sortInjection Mock.testSort
                $ mkDomainBuiltinMap [(Mock.a, mkElemVar Mock.x)]
            testMapA =
                Mock.sortInjection Mock.testSort
                $ mkDomainBuiltinMap [(Mock.a, Mock.a)]
            expect =
                OrPattern.fromPatterns
                    [ Pattern.Conditional
                        { term = Mock.functionalConstr20 Mock.a testMapX
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (ElemVar Mock.x, Mock.a)
                            , (ElemVar Mock.y, testMapA)
                            ]
                        }
                    ]
        actual <-
            (evaluate . Pattern.fromTermLike)
                (mkAnd
                    (Mock.functionalConstr20 (mkElemVar Mock.x) testMapX)
                    (Mock.functionalConstr20 Mock.a (mkElemVar Mock.y))
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
                $ mkDomainBuiltinList [Mock.a, mkElemVar Mock.x]
            testListA =
                Mock.sortInjection Mock.testSort
                $ mkDomainBuiltinList [Mock.a, Mock.a]
            expect =
                OrPattern.fromPatterns
                    [ Pattern.Conditional
                        { term = Mock.functionalConstr20 Mock.a testListX
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (ElemVar Mock.x, Mock.a)
                            , (ElemVar Mock.y, testListA)
                            ]
                        }
                    ]
        actual <-
            (evaluate . Pattern.fromTermLike)
                (mkAnd
                    (Mock.functionalConstr20 (mkElemVar Mock.x) testListX)
                    (Mock.functionalConstr20 Mock.a (mkElemVar Mock.y))
                )
        assertEqual
            "Expected substitution applied to List elements"
            expect
            actual
    ]
  where
    mkDomainBuiltinList = Mock.builtinList

evaluate :: Pattern Variable -> IO (OrPattern Variable)
evaluate = evaluateWithAxioms Map.empty

evaluateWithAxioms
    :: BuiltinAndAxiomSimplifierMap
    -> Pattern Variable
    -> IO (OrPattern Variable)
evaluateWithAxioms axioms = runSimplifier env . Pattern.simplify
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
            , builtinEvaluation Map.evalConcat
            )
        ,   ( AxiomIdentifier.Application Mock.elementMapId
            , builtinEvaluation Map.evalElement
            )
        ,   ( AxiomIdentifier.Application Mock.unitMapId
            , builtinEvaluation Map.evalUnit
            )
        ,   ( AxiomIdentifier.Application Mock.concatSetId
            , builtinEvaluation Set.evalConcat
            )
        ,   ( AxiomIdentifier.Application Mock.concatSetId
            , builtinEvaluation Set.evalConcat
            )
        ,   ( AxiomIdentifier.Application Mock.elementSetId
            , builtinEvaluation Set.evalElement
            )
        ,   ( AxiomIdentifier.Application Mock.unitSetId
            , builtinEvaluation Set.evalUnit
            )
        ,   ( AxiomIdentifier.Application Mock.concatListId
            , builtinEvaluation List.evalConcat
            )
        ,   ( AxiomIdentifier.Application Mock.elementListId
            , builtinEvaluation List.evalElement
            )
        ,   ( AxiomIdentifier.Application Mock.unitListId
            , builtinEvaluation List.evalUnit
            )
        ,   ( AxiomIdentifier.Application Mock.concatListId
            , builtinEvaluation List.evalConcat
            )
        ,   ( AxiomIdentifier.Application Mock.tdivIntId
            , builtinEvaluation (Int.builtinFunctions Map.! Int.tdivKey)
            )
        ]

axiom
    :: TermLike Variable
    -> TermLike Variable
    -> Predicate.Predicate Variable
    -> EqualityRule Variable
axiom left right predicate =
    EqualityRule RulePattern
        { left
        , antiLeft = Nothing
        , right
        , requires = predicate
        , ensures = makeTruePredicate
        , attributes = Default.def
        }

-- | Specialize 'Set.builtinSet' to the builtin sort 'setSort'.
asInternal :: Set.Set (TermLike Concrete) -> TermLike Variable
asInternal =
    Ac.asInternalConcrete Mock.metadataTools Mock.setSort
    . Map.fromSet (const Domain.SetValue)
