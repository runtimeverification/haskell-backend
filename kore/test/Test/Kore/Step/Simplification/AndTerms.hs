module Test.Kore.Step.Simplification.AndTerms where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
       ( testCase )

import           Control.Error
                 ( MaybeT (..) )
import qualified Control.Error as Error
import           Data.Default
                 ( Default (..) )
import qualified Data.Map as Map

import qualified Kore.Attribute.Axiom as Attribute
import           Kore.Attribute.Simplification
                 ( Simplification (Simplification) )
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import qualified Kore.Internal.MultiOr as MultiOr
                 ( extractPatterns )
import           Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike
import           Kore.Predicate.Predicate
                 ( makeCeilPredicate, makeEqualsPredicate, makeFalsePredicate,
                 makeTruePredicate )
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
import           Kore.Step.Axiom.Registry
                 ( axiomPatternsToEvaluators )
import           Kore.Step.Rule
                 ( EqualityRule (EqualityRule), RulePattern (RulePattern) )
import qualified Kore.Step.Rule as RulePattern
                 ( RulePattern (..) )
import           Kore.Step.Simplification.AndTerms
                 ( termAnd, termEquals, termUnification )
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import qualified Kore.Step.Simplification.Data as BranchT
                 ( gather )
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import qualified Kore.Syntax.Pattern as AST
import qualified Kore.Unification.Substitution as Substitution
import qualified Kore.Unification.Unify as Monad.Unify
import qualified SMT

import           Test.Kore
import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSimplifiers as Mock
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_andTermsSimplification :: [TestTree]
test_andTermsSimplification =
    [ testGroup "Predicates"
        [ testCase "\\and{s}(f{}(a), \\top{s}())" $ do
            let expected =
                    Conditional
                        { term = fOfA
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            actual <- simplifyUnify Mock.metadataTools fOfA mkTop_
            assertEqualWithExplanation "" ([expected], Just [expected]) actual

        , testCase "\\and{s}(\\top{s}(), f{}(a))" $ do
            let expected =
                    Conditional
                        { term = fOfA
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            actual <- simplifyUnify Mock.metadataTools mkTop_ fOfA
            assertEqualWithExplanation "" ([expected], Just [expected]) actual

        , testCase "\\and{s}(f{}(a), \\bottom{s}())" $ do
            let expect =
                    ( [Pattern.bottom]
                    , Just [Pattern.bottom]
                    )
            actual <- simplifyUnify Mock.metadataTools fOfA mkBottom_
            assertEqualWithExplanation "" expect actual

        , testCase "\\and{s}(\\bottom{s}(), f{}(a))" $ do
            let expect =
                    ( [Pattern.bottom]
                    , Just [Pattern.bottom]
                    )
            actual <-
                simplifyUnify
                    Mock.metadataTools
                    mkBottom_
                    fOfA
            assertEqualWithExplanation "" expect actual
        ]

    , testCase "equal patterns and" $ do
        let expect =
                Conditional
                    { term = fOfA
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            simplifyUnify
                Mock.metadataTools
                fOfA fOfA
        assertEqualWithExplanation "" ([expect], Just [expect]) actual

    , testGroup "variable function and"
        [ testCase "\\and{s}(x:s, f{}(a))" $ do
            let expect =
                    Conditional
                        { term = fOfA
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap [(Mock.x, fOfA)]
                        }
            actual <-
                simplifyUnify
                    Mock.metadataTools
                    (mkVar Mock.x) fOfA
            assertEqualWithExplanation "" ([expect], Just [expect]) actual

        , testCase "\\and{s}(f{}(a), x:s)" $ do
            let expect =
                    Conditional
                        { term = fOfA
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap [(Mock.x, fOfA)]
                        }
            actual <-
                simplifyUnify
                    Mock.metadataTools
                    fOfA (mkVar Mock.x)
            assertEqualWithExplanation "" ([expect], Just [expect]) actual
        ]

    , testGroup "injective head and"
        [ testCase "same head, different child" $ do
            let expect =
                    Conditional
                        { term = Mock.injective10 fOfA
                        , predicate = makeEqualsPredicate fOfA gOfA
                        , substitution = mempty
                        }
            actual <-
                simplifyUnify
                    Mock.metadataTools
                    (Mock.injective10 fOfA) (Mock.injective10 gOfA)
            assertEqualWithExplanation "" ([expect], Just [expect]) actual
        , testCase "same head, same child" $ do
            let expected =
                    Conditional
                        { term = Mock.injective10 fOfA
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            actual <-
                simplifyUnify
                    Mock.metadataTools
                    (Mock.injective10 fOfA) (Mock.injective10 fOfA)
            assertEqualWithExplanation "" ([expected], Just [expected]) actual
        , testCase "different head" $ do
            let expect =
                    (   [ Conditional
                            { term =
                                mkAnd
                                    (Mock.injective10 fOfA)
                                    (Mock.injective11 gOfA)
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                        ]
                    , Nothing
                    )
            actual <-
                simplifyUnify
                    Mock.metadataTools
                    (Mock.injective10 fOfA) (Mock.injective11 gOfA)
            assertEqualWithExplanation "" expect actual
        ]

    , testGroup "sort injection and"
        [ testCase "same head, different child" $ do
            let expect =
                    Conditional
                        { term = Mock.sortInjection10 Mock.cfSort0
                        , predicate =
                            makeEqualsPredicate Mock.cfSort0 Mock.cgSort0
                        , substitution = mempty
                        }
            actual <-
                simplifyUnify
                    Mock.metadataTools
                    (Mock.sortInjection10 Mock.cfSort0)
                    (Mock.sortInjection10 Mock.cgSort0)
            assertEqualWithExplanation "" ([expect], Just [expect]) actual
        , testCase "same head, same child" $ do
            let expect =
                    Conditional
                        { term =
                            Mock.sortInjection10 Mock.cfSort0
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            actual <-
                simplifyUnify
                    Mock.metadataTools
                    (Mock.sortInjection10 Mock.cfSort0)
                    (Mock.sortInjection10 Mock.cfSort0)
            assertEqualWithExplanation "" ([expect], Just [expect]) actual
        , testCase "different head, not subsort" $ do
            let expect =
                    ([Pattern.bottom], Just [Pattern.bottom])
            actual <-
                simplifyUnify
                    Mock.metadataTools
                    (Mock.sortInjectionSubToTop Mock.plain00Subsort)
                    (Mock.sortInjection0ToTop Mock.plain00Sort0)
            assertEqualWithExplanation "" expect actual
        , testCase "different head, subsort first" $ do
            let expect =
                    (   [ Conditional
                            { term =
                                Mock.sortInjectionSubToTop
                                    (mkAnd
                                        (Mock.sortInjectionSubSubToSub
                                            Mock.plain00SubSubsort
                                        )
                                        Mock.plain00Subsort
                                    )
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                        ]
                    , Nothing
                    )
            actual <-
                simplifyUnify
                    Mock.metadataTools
                    (Mock.sortInjectionSubSubToTop Mock.plain00SubSubsort)
                    (Mock.sortInjectionSubToTop Mock.plain00Subsort)
            assertEqualWithExplanation "" expect actual
        , testCase "different head, subsort second" $ do
            let expect =
                    (   [ Conditional
                            { term =
                                Mock.sortInjectionSubToTop
                                    (mkAnd
                                        Mock.plain00Subsort
                                        (Mock.sortInjectionSubSubToSub
                                            Mock.plain00SubSubsort
                                        )
                                    )
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                        ]
                    , Nothing
                    )
            actual <-
                simplifyUnify
                    Mock.metadataTools
                    (Mock.sortInjectionSubToTop Mock.plain00Subsort)
                    (Mock.sortInjectionSubSubToTop Mock.plain00SubSubsort)
            assertEqualWithExplanation "" expect actual
        , testCase "different head constructors not subsort" $ do
            let expect =
                    ( [Pattern.bottom]
                    , Just [Pattern.bottom]
                    )
            actual <-
                simplifyUnify
                    Mock.metadataTools
                    (Mock.sortInjection10 Mock.aSort0)
                    (Mock.sortInjection11 Mock.aSort1)
            assertEqualWithExplanation "" expect actual
        , testCase "different head constructors subsort" $ do
            let expect =
                    ( [Pattern.bottom]
                    , Just [Pattern.bottom]
                    )
            actual <-
                simplifyUnify
                    Mock.metadataTools
                    (Mock.sortInjectionSubToTop Mock.aSubsort)
                    (Mock.sortInjectionSubSubToTop Mock.aSubSubsort)
            assertEqualWithExplanation "" expect actual
        , testCase "different head constructors common subsort" $ do
            let expect =
                    ( [Pattern.bottom]
                    , Just [Pattern.bottom]
                    )
            actual <-
                simplifyUnify
                    Mock.metadataTools
                    (Mock.sortInjectionOtherToTop Mock.aOtherSort)
                    (Mock.sortInjectionSubToTop Mock.aSubsort)
            assertEqualWithExplanation "" expect actual
        , testCase "different head constructors common subsort reversed" $ do
            let expect =
                    ( [Pattern.bottom]
                    , Just [Pattern.bottom]
                    )
            actual <-
                simplifyUnify
                    Mock.metadataTools
                    (Mock.sortInjectionSubToTop Mock.aSubsort)
                    (Mock.sortInjectionOtherToTop Mock.aOtherSort)
            assertEqualWithExplanation "" expect actual
        ]

    , testGroup "constructor and"
        [ testCase "same head" $ do
            let expect =
                    let
                        expected = Conditional
                            { term = Mock.constr10 Mock.cf
                            , predicate = makeEqualsPredicate Mock.cf Mock.cg
                            , substitution = mempty
                            }
                    in ([expected], Just [expected])
            actual <-
                simplifyUnify
                    Mock.metadataTools
                    (Mock.constr10 Mock.cf)
                    (Mock.constr10 Mock.cg)
            assertEqualWithExplanation "" expect actual

        , testCase "same head same child" $ do
            let expect =
                    let
                        expected = Conditional
                            { term = Mock.constr10 Mock.cf
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                    in ([expected], Just [expected])
            actual <-
                simplifyUnify
                    Mock.metadataTools
                    (Mock.constr10 Mock.cf)
                    (Mock.constr10 Mock.cf)
            assertEqualWithExplanation "" expect actual

        , testCase "different head" $ do
            let expect =
                    ( [Pattern.bottom]
                    , Just [Pattern.bottom]
                    )
            actual <-
                simplifyUnify
                    Mock.metadataTools
                    (Mock.constr10 Mock.cf)
                    (Mock.constr11 Mock.cf)
            assertEqualWithExplanation "" expect actual
        ]

    , testCase "constructor-sortinjection and" $ do
        let expect =
                ( [Pattern.bottom]
                , Just [Pattern.bottom]
                )
        actual <-
            simplifyUnify
                Mock.metadataTools
                (Mock.constr10 Mock.cf)
                (Mock.sortInjection11 Mock.cfSort1)
        assertEqualWithExplanation "" expect actual

    , testGroup "domain value and"
        [ testCase "equal values" $ do
            let expect =
                    let
                        expected = Conditional
                            { term = aDomainValue
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                    in ([expected], Just [expected])
            actual <-
                simplifyUnify
                    Mock.metadataTools
                    aDomainValue aDomainValue
            assertEqualWithExplanation "" expect actual

        , testCase "different values" $ do
            let expect =
                    ( [Pattern.bottom]
                    , Just [Pattern.bottom]
                    )
            actual <-
                simplifyUnify
                    Mock.metadataTools
                    aDomainValue bDomainValue
            assertEqualWithExplanation "" expect actual
        ]

    , testGroup "string literal and"
        [ testCase "equal values" $ do
            let expect =
                    let
                        expected = Conditional
                            { term = mkStringLiteral "a"
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                    in ([expected], Just [expected])
            actual <-
                simplifyUnify
                    Mock.emptyMetadataTools
                    (mkStringLiteral "a")
                    (mkStringLiteral "a")
            assertEqualWithExplanation "" expect actual

        , testCase "different values" $ do
            let expect =
                    ( [Pattern.bottom]
                    , Just [Pattern.bottom]
                    )
            actual <-
                simplifyUnify
                    Mock.emptyMetadataTools
                    (mkStringLiteral "a")
                    (mkStringLiteral "b")
            assertEqualWithExplanation "" expect actual
        ]

    , testGroup "char literal and"
        [ testCase "equal values" $ do
            let expect =
                    let
                        expected = Conditional
                            { term = mkCharLiteral 'a'
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                    in ([expected], Just [expected])
            actual <-
                simplifyUnify
                    Mock.emptyMetadataTools
                    (mkCharLiteral 'a')
                    (mkCharLiteral 'a')
            assertEqualWithExplanation "" expect actual

        , testCase "different values" $ do
            let expect =
                    ( [Pattern.bottom]
                    , Just [Pattern.bottom]
                    )
            actual <-
                simplifyUnify
                    Mock.emptyMetadataTools
                    (mkCharLiteral 'a')
                    (mkCharLiteral 'b')
            assertEqualWithExplanation "" expect actual
        ]

    , testGroup "function and"
        [ testCase "equal values" $ do
            let expect =
                    let
                        expanded = Conditional
                            { term = fOfA
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                    in ([expanded], Just [expanded])
            actual <-
                simplifyUnify
                    Mock.metadataTools
                    fOfA fOfA
            assertEqualWithExplanation "" expect actual

        , testCase "not equal values" $ do
            let expect =
                    let
                        expanded = Conditional
                            { term = fOfA
                            , predicate = makeEqualsPredicate fOfA gOfA
                            , substitution = mempty
                            }
                    in ([expanded], Just [expanded])
            actual <-
                simplifyUnify
                    Mock.metadataTools
                    fOfA gOfA
            assertEqualWithExplanation "" expect actual
        ]

    , testGroup "unhandled cases"
        [ testCase "top level" $ do
            let expect =
                    (   [ Conditional
                            { term = mkAnd plain0OfA plain1OfA
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                        ]
                    , Nothing
                    )
            actual <-
                simplifyUnify
                    Mock.metadataTools
                    plain0OfA plain1OfA
            assertEqualWithExplanation "" expect actual

        , testCase "one level deep" $ do
            let expect =
                    (   [ Conditional
                            { term = Mock.constr10 (mkAnd plain0OfA plain1OfA)
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                        ]
                    , Nothing
                    )
            actual <-
                simplifyUnify
                    Mock.metadataTools
                    (Mock.constr10 plain0OfA) (Mock.constr10 plain1OfA)
            assertEqualWithExplanation "" expect actual

        , testCase "two levels deep" $ do
            let expect =
                    (   [ Conditional
                            { term =
                                Mock.constr10
                                    (Mock.constr10 (mkAnd plain0OfA plain1OfA))
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                        ]
                    , Nothing
                    )
            actual <-
                simplifyUnify
                    Mock.metadataTools
                    (Mock.constr10 (Mock.constr10 plain0OfA))
                    (Mock.constr10 (Mock.constr10 plain1OfA))
            assertEqualWithExplanation "" expect actual
        ]

    , testCase "binary constructor of non-specialcased values" $ do
        let expect =
                (   [ Conditional
                        { term =
                            Mock.functionalConstr20
                                (mkAnd plain0OfA plain1OfA)
                                (mkAnd plain0OfB plain1OfB)
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
                , Nothing
                )
        actual <-
            simplifyUnify
                Mock.metadataTools
                (Mock.functionalConstr20 plain0OfA plain0OfB)
                (Mock.functionalConstr20 plain1OfA plain1OfB)
        assertEqualWithExplanation "" expect actual

    , testGroup "builtin Map domain"
        [ testCase "concrete Map, same keys" $ do
            let expect = Just
                    [ Conditional
                        { term = Mock.builtinMap [(Mock.aConcrete, Mock.b)]
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap [(Mock.x, Mock.b)]
                        }
                    ]
            actual <-
                unify
                    Mock.metadataTools
                    (Mock.builtinMap [(Mock.aConcrete, Mock.b)])
                    (Mock.builtinMap [(Mock.aConcrete, mkVar Mock.x)])
            assertEqualWithExplanation "" expect actual

        , testCase "concrete Map, different keys" $ do
            let expect = Just [Pattern.bottom]
            actual <-
                unify
                    Mock.metadataTools
                    (Mock.builtinMap [(Mock.aConcrete, Mock.b)])
                    (Mock.builtinMap [(Mock.bConcrete, mkVar Mock.x)])
            assertEqualWithExplanation "" expect actual

        , testCase "concrete Map with framed Map" $ do
            let expect = Just
                    [ Conditional
                        { term =
                            Mock.builtinMap
                                [ (Mock.aConcrete, fOfA)
                                , (Mock.bConcrete, fOfB)
                                ]
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap
                            [ (Mock.x, fOfA)
                            , (Mock.m, Mock.builtinMap [(Mock.bConcrete, fOfB)])
                            ]
                        }
                    ]
            actual <-
                unify
                    Mock.metadataTools
                    (Mock.builtinMap
                        [ (Mock.aConcrete, fOfA)
                        , (Mock.bConcrete, fOfB)
                        ]
                    )
                    (Mock.concatMap
                        (Mock.builtinMap [(Mock.aConcrete, mkVar Mock.x)])
                        (mkVar Mock.m)
                    )
            assertEqualWithExplanation "" expect actual

        , testCase "concrete Map with framed Map" $ do
            let expect = Just
                    [ Conditional
                        { term =
                            Mock.builtinMap
                                [ (Mock.aConcrete, fOfA)
                                , (Mock.bConcrete, fOfB)
                                ]
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap
                            [ (Mock.x, fOfA)
                            , (Mock.m, Mock.builtinMap [(Mock.bConcrete, fOfB)])
                            ]
                        }
                    ]
            actual <-
                unify
                    Mock.metadataTools
                    (Mock.builtinMap
                        [ (Mock.aConcrete, fOfA)
                        , (Mock.bConcrete, fOfB)
                        ]
                    )
                    (Mock.concatMap
                        (mkVar Mock.m)
                        (Mock.builtinMap [(Mock.aConcrete, mkVar Mock.x)])
                    )
            assertEqualWithExplanation "" expect actual

        , testCase "framed Map with concrete Map" $ do
            let expect = Just
                    [ Conditional
                        { term =
                            Mock.builtinMap
                                [ (Mock.aConcrete, fOfA)
                                , (Mock.bConcrete, fOfB)
                                ]
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap
                            [ (Mock.x, fOfA)
                            , (Mock.m, Mock.builtinMap [(Mock.bConcrete, fOfB)])
                            ]
                        }
                    ]
            actual <-
                unify
                    Mock.metadataTools
                    (Mock.concatMap
                        (Mock.builtinMap [(Mock.aConcrete, mkVar Mock.x)])
                        (mkVar Mock.m)
                    )
                    (Mock.builtinMap
                        [ (Mock.aConcrete, fOfA)
                        , (Mock.bConcrete, fOfB)
                        ]
                    )
            assertEqualWithExplanation "" expect actual

        , testCase "framed Map with concrete Map" $ do
            let expect = Just
                    [ Conditional
                        { term =
                            Mock.builtinMap
                                [ (Mock.aConcrete, fOfA)
                                , (Mock.bConcrete, fOfB)
                                ]
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap
                            [ (Mock.x, fOfA)
                            , (Mock.m, Mock.builtinMap [(Mock.bConcrete, fOfB)])
                            ]
                        }
                    ]
            actual <-
                unify
                    Mock.metadataTools
                    (Mock.concatMap
                        (mkVar Mock.m)
                        (Mock.builtinMap [(Mock.aConcrete, mkVar Mock.x)])
                    )
                    (Mock.builtinMap
                        [ (Mock.aConcrete, fOfA)
                        , (Mock.bConcrete, fOfB)
                        ]
                    )
            assertEqualWithExplanation "" expect actual
        -- TODO: Add tests with non-trivial predicates.
        ]

    , testGroup "builtin List domain"
        [ testCase "[same head, same head]" $ do
            let term1 =
                    Mock.builtinList
                        [ Mock.constr10 Mock.cf
                        , Mock.constr11 Mock.cf
                        ]
                expect = Just
                    [ Conditional
                        { term = term1
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
            actual <- unify Mock.metadataTools term1 term1
            assertEqualWithExplanation "" expect actual

        , testCase "[same head, different head]" $ do
            let term3 = Mock.builtinList [Mock.a, Mock.a]
                term4 = Mock.builtinList [Mock.a, Mock.b]
                expect = Just
                    [ Conditional
                        { term = Mock.builtinList [Mock.a, mkBottom_]
                        , predicate = makeFalsePredicate
                        , substitution = mempty
                        }
                    ]
            actual <- unify Mock.metadataTools term3 term4
            assertEqualWithExplanation "" expect actual

        , testCase "[a] `concat` x /\\ [a, b] " $ do
            let term5 = Mock.concatList
                        (Mock.builtinList [Mock.a])
                        (mkVar Mock.x)
                term6 = Mock.builtinList [Mock.a, Mock.b]
                expect = Just
                    [ Conditional
                        { term = Mock.builtinList [Mock.a, Mock.b]
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [(Mock.x, Mock.builtinList [Mock.b])]
                        }
                    ]
            actual <- unify Mock.metadataTools term5 term6
            assertEqualWithExplanation "" expect actual

        , testCase "different lengths" $ do
            let term7 = Mock.builtinList [Mock.a, Mock.a]
                term8 = Mock.builtinList [Mock.a]
                expect = Just [Pattern.bottom]
            actual <- unify Mock.metadataTools term7 term8
            assertEqualWithExplanation "" expect actual

        -- TODO: Add tests with non-trivial unifications and predicates.
        ]
    -- TODO: Add tests for set unification.
    ]

test_equalsTermsSimplification :: [TestTree]
test_equalsTermsSimplification =
    [ testCase "adds ceil when producing substitutions" $ do
        let expected = Just
                [ Conditional
                    { term = ()
                    , predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.unsafeWrap [(Mock.x, Mock.cf)]
                    }
                ]
        actual <- simplifyEquals
            Mock.metadataTools Map.empty (mkVar Mock.x) Mock.cf
        assertEqualWithExplanation "" expected actual
    , testCase "handles ambiguity" $ do
        let
            expected = Just
                [ Conditional
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [(Mock.x, Mock.cf), (Mock.y, Mock.a)]
                    }
                , Conditional
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [(Mock.x, Mock.cf), (Mock.y, Mock.b)]
                    }
                ]
            sortVar = SortVariableSort (SortVariable (testId "S"))
            simplifiers = axiomPatternsToEvaluators $ Map.fromList
                [   (   AxiomIdentifier.Ceil
                            (AxiomIdentifier.Application Mock.cfId)
                    ,   [ EqualityRule RulePattern
                            { left = mkCeil sortVar Mock.cf
                            , right =
                                mkOr
                                    (mkEquals_ (mkVar Mock.y) Mock.a)
                                    (mkEquals_ (mkVar Mock.y) Mock.b)
                            , requires = makeTruePredicate
                            , ensures = makeTruePredicate
                            , attributes = def
                                {Attribute.simplification = Simplification True}
                            }
                        ]
                    )
                ]
        actual <- simplifyEquals
            Mock.metadataTools simplifiers (mkVar Mock.x) Mock.cf
        assertEqualWithExplanation "" expected actual
    , testCase "handles multiple ambiguity" $ do
        let
            expected = Just
                [ Conditional
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [ (Mock.x, Mock.cf), (Mock.var_x_1, Mock.cg)
                        , (Mock.y, Mock.a), (Mock.z, Mock.a)
                        ]
                    }
                , Conditional
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [ (Mock.x, Mock.cf), (Mock.var_x_1, Mock.cg)
                        , (Mock.y, Mock.a), (Mock.z, Mock.b)
                        ]
                    }
                , Conditional
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [ (Mock.x, Mock.cf), (Mock.var_x_1, Mock.cg)
                        , (Mock.y, Mock.b), (Mock.z, Mock.a)
                        ]
                    }
                , Conditional
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [ (Mock.x, Mock.cf), (Mock.var_x_1, Mock.cg)
                        , (Mock.y, Mock.b), (Mock.z, Mock.b)
                        ]
                    }
                ]
            sortVar = SortVariableSort (SortVariable (testId "S"))
            simplifiers = axiomPatternsToEvaluators $ Map.fromList
                [   (   AxiomIdentifier.Ceil
                            (AxiomIdentifier.Application Mock.cfId)
                    ,   [ EqualityRule RulePattern
                            { left = mkCeil sortVar Mock.cf
                            , right =
                                mkOr
                                    (mkEquals_ (mkVar Mock.y) Mock.a)
                                    (mkEquals_ (mkVar Mock.y) Mock.b)
                            , requires = makeTruePredicate
                            , ensures = makeTruePredicate
                            , attributes = def
                                {Attribute.simplification = Simplification True}
                            }
                        ]
                    )
                ,   (   AxiomIdentifier.Ceil
                            (AxiomIdentifier.Application Mock.cgId)
                    ,   [ EqualityRule RulePattern
                            { left = mkCeil sortVar Mock.cg
                            , right =
                                mkOr
                                    (mkEquals_ (mkVar Mock.z) Mock.a)
                                    (mkEquals_ (mkVar Mock.z) Mock.b)
                            , requires = makeTruePredicate
                            , ensures = makeTruePredicate
                            , attributes = def
                                {Attribute.simplification = Simplification True}
                            }
                        ]
                    )
                ]
        actual <- simplifyEquals
            Mock.metadataTools simplifiers
            (Mock.functionalConstr20 (mkVar Mock.x) (mkVar Mock.var_x_1))
            (Mock.functionalConstr20 Mock.cf Mock.cg)
        assertEqualWithExplanation "" expected actual
    ]

fOfA :: TermLike Variable
fOfA = Mock.f Mock.a

fOfB :: TermLike Variable
fOfB = Mock.f Mock.b

gOfA :: TermLike Variable
gOfA = Mock.g Mock.a

plain0OfA :: TermLike Variable
plain0OfA = Mock.plain10 Mock.a

plain1OfA :: TermLike Variable
plain1OfA = Mock.plain11 Mock.a

plain0OfB :: TermLike Variable
plain0OfB = Mock.plain10 Mock.b

plain1OfB :: TermLike Variable
plain1OfB = Mock.plain11 Mock.b

aDomainValue :: TermLike Variable
aDomainValue =
    mkDomainValue $ Domain.BuiltinExternal Domain.External
        { domainValueSort = Mock.testSort
        , domainValueChild = AST.eraseAnnotations $ mkStringLiteral "a"
        }

bDomainValue :: TermLike Variable
bDomainValue =
    mkDomainValue $ Domain.BuiltinExternal Domain.External
        { domainValueSort = Mock.testSort
        , domainValueChild = AST.eraseAnnotations $ mkStringLiteral "b"
        }

simplifyUnify
    :: SmtMetadataTools StepperAttributes
    -> TermLike Variable
    -> TermLike Variable
    -> IO ([Pattern Variable], Maybe [Pattern Variable])
simplifyUnify tools first second =
    (,)
        <$> simplify tools first second
        <*> unify tools first second

unify
    :: SmtMetadataTools StepperAttributes
    -> TermLike Variable
    -> TermLike Variable
    -> IO (Maybe [Pattern Variable])
unify tools first second =
    SMT.runSMT SMT.defaultConfig
    $ evalSimplifier emptyLogger
    $ runMaybeT unification
  where
    substitutionSimplifier = Mock.substitutionSimplifier tools
    unification =
        -- The unification error is discarded because, for testing purposes, we
        -- are not interested in the /reason/ unification failed. For the tests,
        -- the failure is almost always due to unsupported patterns anyway.
        MaybeT . fmap Error.hush . Monad.Unify.runUnifier $ termUnification
            tools
            substitutionSimplifier
            (Simplifier.create tools Map.empty)
            Map.empty
            first
            second

simplify
    :: SmtMetadataTools StepperAttributes
    -> TermLike Variable
    -> TermLike Variable
    -> IO [Pattern Variable]
simplify tools first second =
    SMT.runSMT SMT.defaultConfig
    $ evalSimplifier emptyLogger
    $ BranchT.gather
    $ termAnd
        tools
        (Mock.substitutionSimplifier tools)
        (Simplifier.create tools Map.empty)
        Map.empty
        first
        second

simplifyEquals
    :: SmtMetadataTools StepperAttributes
    -> BuiltinAndAxiomSimplifierMap
    -> TermLike Variable
    -> TermLike Variable
    -> IO (Maybe [Predicate Variable])
simplifyEquals tools axiomIdToSimplifier first second =
    fmap MultiOr.extractPatterns
    <$> SMT.runSMT SMT.defaultConfig
        ( evalSimplifier emptyLogger
        $ runMaybeT
        $ termEquals
            tools
            (Mock.substitutionSimplifier tools)
            (Simplifier.create tools axiomIdToSimplifier)
            axiomIdToSimplifier
            first
            second
        )
