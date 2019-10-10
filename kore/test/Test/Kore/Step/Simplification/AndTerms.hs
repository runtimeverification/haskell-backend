module Test.Kore.Step.Simplification.AndTerms where

import Test.Tasty

import Control.Error
    ( MaybeT (..)
    )
import qualified Control.Error as Error
import Data.Default
    ( Default (..)
    )
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text
    ( Text
    )

import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Simplification
    ( Simplification (Simplification)
    )
import qualified Kore.Builtin.AssociativeCommutative as Ac
import qualified Kore.Domain.Builtin as Domain
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.MultiOr as MultiOr
    ( extractPatterns
    )
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike as TermLike
import Kore.Predicate.Predicate
    ( makeAndPredicate
    , makeCeilPredicate
    , makeEqualsPredicate
    , makeTruePredicate
    )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
import Kore.Step.Axiom.Registry
    ( axiomPatternsToEvaluators
    )
import Kore.Step.Rule
    ( EqualityRule (EqualityRule)
    , RulePattern (RulePattern)
    )
import qualified Kore.Step.Rule as RulePattern
    ( RulePattern (..)
    )
import Kore.Step.Simplification.AndTerms
    ( functionAnd
    , termAnd
    , termEquals
    , termUnification
    )
import Kore.Step.Simplification.Simplify
import Kore.Syntax.Sentence
    ( SentenceAlias
    )
import qualified Kore.Unification.Substitution as Substitution
import qualified Kore.Unification.Unify as Monad.Unify
import Kore.Unparser
    ( Unparse
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import Test.Kore
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext

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
            actual <- simplifyUnify fOfA mkTop_
            assertEqual "" ([expected], Just [expected]) actual

        , testCase "\\and{s}(\\top{s}(), f{}(a))" $ do
            let expected =
                    Conditional
                        { term = fOfA
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            actual <- simplifyUnify mkTop_ fOfA
            assertEqual "" ([expected], Just [expected]) actual

        , testCase "\\and{s}(f{}(a), \\bottom{s}())" $ do
            let expect =
                    ( [Pattern.bottom]
                    , Just [Pattern.bottom]
                    )
            actual <- simplifyUnify fOfA mkBottom_
            assertEqual "" expect actual

        , testCase "\\and{s}(\\bottom{s}(), f{}(a))" $ do
            let expect =
                    ( [Pattern.bottom]
                    , Just [Pattern.bottom]
                    )
            actual <- simplifyUnify mkBottom_ fOfA
            assertEqual "" expect actual
        ]

    , testCase "equal patterns and" $ do
        let expect =
                Conditional
                    { term = fOfA
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <- simplifyUnify fOfA fOfA
        assertEqual "" ([expect], Just [expect]) actual

    , testGroup "variable function and"
        [ testCase "\\and{s}(x:s, f{}(a))" $ do
            let expect =
                    Conditional
                        { term = fOfA
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap [(ElemVar Mock.x, fOfA)]
                        }
            actual <- simplifyUnify (mkElemVar Mock.x) fOfA
            assertEqual "" ([expect], Just [expect]) actual

        , testCase "\\and{s}(f{}(a), x:s)" $ do
            let expect =
                    Conditional
                        { term = fOfA
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap [(ElemVar Mock.x, fOfA)]
                        }
            actual <- simplifyUnify fOfA (mkElemVar Mock.x)
            assertEqual "" ([expect], Just [expect]) actual
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
                    (Mock.injective10 fOfA) (Mock.injective10 gOfA)
            assertEqual "" ([expect], Just [expect]) actual
        , testCase "same head, same child" $ do
            let expected =
                    Conditional
                        { term = Mock.injective10 fOfA
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            actual <-
                simplifyUnify
                    (Mock.injective10 fOfA) (Mock.injective10 fOfA)
            assertEqual "" ([expected], Just [expected]) actual
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
                    (Mock.injective10 fOfA) (Mock.injective11 gOfA)
            assertEqual "" expect actual
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
                    (Mock.sortInjection10 Mock.cfSort0)
                    (Mock.sortInjection10 Mock.cgSort0)
            assertEqual "" ([expect], Just [expect]) actual
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
                    (Mock.sortInjection10 Mock.cfSort0)
                    (Mock.sortInjection10 Mock.cfSort0)
            assertEqual "" ([expect], Just [expect]) actual
        , testCase "different head, not subsort" $ do
            let expect = ([], Just [])
            actual <-
                simplifyUnify
                    (Mock.sortInjectionSubToTop Mock.plain00Subsort)
                    (Mock.sortInjection0ToTop Mock.plain00Sort0)
            assertEqual "" expect actual
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
                    (Mock.sortInjectionSubSubToTop Mock.plain00SubSubsort)
                    (Mock.sortInjectionSubToTop Mock.plain00Subsort)
            assertEqual "" expect actual
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
                    (Mock.sortInjectionSubToTop Mock.plain00Subsort)
                    (Mock.sortInjectionSubSubToTop Mock.plain00SubSubsort)
            assertEqual "" expect actual
        , testCase "different head constructors not subsort" $ do
            let expect = ([], Just [])
            actual <-
                simplifyUnify
                    (Mock.sortInjection10 Mock.aSort0)
                    (Mock.sortInjection11 Mock.aSort1)
            assertEqual "" expect actual
        , testCase "different head constructors subsort" $ do
            let expect = ([], Just [])
            actual <-
                simplifyUnify
                    (Mock.sortInjectionSubToTop Mock.aSubsort)
                    (Mock.sortInjectionSubSubToTop Mock.aSubSubsort)
            assertEqual "" expect actual
        , testCase "different head constructors common subsort" $ do
            let expect = ([], Just [])
            actual <-
                simplifyUnify
                    (Mock.sortInjectionOtherToTop Mock.aOtherSort)
                    (Mock.sortInjectionSubToTop Mock.aSubsort)
            assertEqual "" expect actual
        , testCase "different head constructors common subsort reversed" $ do
            let expect = ([], Just [])
            actual <-
                simplifyUnify
                    (Mock.sortInjectionSubToTop Mock.aSubsort)
                    (Mock.sortInjectionOtherToTop Mock.aOtherSort)
            assertEqual "" expect actual
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
                    (Mock.constr10 Mock.cf)
                    (Mock.constr10 Mock.cg)
            assertEqual "" expect actual

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
                    (Mock.constr10 Mock.cf)
                    (Mock.constr10 Mock.cf)
            assertEqual "" expect actual

        , testCase "different head" $ do
            let expect = ([], Just [])
            actual <-
                simplifyUnify
                    (Mock.constr10 Mock.cf)
                    (Mock.constr11 Mock.cf)
            assertEqual "" expect actual
        ]

    , testCase "constructor-sortinjection and" $ do
        let expect = ([], Just [])
        actual <-
            simplifyUnify
                (Mock.constr10 Mock.cf)
                (Mock.sortInjection11 Mock.cfSort1)
        assertEqual "" expect actual

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
            actual <- simplifyUnify aDomainValue aDomainValue
            assertEqual "" expect actual

        , testCase "different values" $ do
            let expect = ([], Just [])
            actual <- simplifyUnify aDomainValue bDomainValue
            assertEqual "" expect actual
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
                    (mkStringLiteral "a")
                    (mkStringLiteral "a")
            assertEqual "" expect actual

        , testCase "different values" $ do
            let expect = ([], Just [])
            actual <-
                simplifyUnify
                    (mkStringLiteral "a")
                    (mkStringLiteral "b")
            assertEqual "" expect actual
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
            actual <- simplifyUnify fOfA fOfA
            assertEqual "" expect actual

        , testCase "not equal values" $ do
            let expect =
                    let
                        expanded = Conditional
                            { term = fOfA
                            , predicate = makeEqualsPredicate fOfA gOfA
                            , substitution = mempty
                            }
                    in ([expanded], Just [expanded])
            actual <- simplifyUnify fOfA gOfA
            assertEqual "" expect actual
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
            actual <- simplifyUnify plain0OfA plain1OfA
            assertEqual "" expect actual

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
                    (Mock.constr10 plain0OfA) (Mock.constr10 plain1OfA)
            assertEqual "" expect actual

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
                    (Mock.constr10 (Mock.constr10 plain0OfA))
                    (Mock.constr10 (Mock.constr10 plain1OfA))
            assertEqual "" expect actual
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
                (Mock.functionalConstr20 plain0OfA plain0OfB)
                (Mock.functionalConstr20 plain1OfA plain1OfB)
        assertEqual "" expect actual

    , testGroup "builtin Map domain"
        [ testCase "concrete Map, same keys" $ do
            let expect = Just
                    [ Conditional
                        { term = Mock.builtinMap [(Mock.a, Mock.b)]
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap [(ElemVar Mock.x, Mock.b)]
                        }
                    ]
            actual <-
                unify
                    (Mock.builtinMap [(Mock.a, Mock.b)])
                    (Mock.builtinMap [(Mock.a, mkElemVar Mock.x)])
            assertEqual "" expect actual

        , testCase "concrete Map, different keys" $ do
            let expect = Just []
            actual <-
                unify
                    (Mock.builtinMap [(Mock.a, Mock.b)])
                    (Mock.builtinMap [(Mock.b, mkElemVar Mock.x)])
            assertEqual "" expect actual

        , testCase "concrete Map with framed Map" $ do
            let expect = Just
                    [ Conditional
                        { term =
                            Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)]
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap
                            [ (ElemVar Mock.x, fOfA)
                            , (ElemVar Mock.m, Mock.builtinMap [(Mock.b, fOfB)])
                            ]
                        }
                    ]
            actual <-
                unify
                    (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
                    (Mock.concatMap
                        (Mock.builtinMap [(Mock.a, mkElemVar Mock.x)])
                        (mkElemVar Mock.m)
                    )
            assertEqual "" expect actual

        , testCase "concrete Map with framed Map" $ do
            let expect = Just
                    [ Conditional
                        { term =
                            Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)]
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap
                            [ (ElemVar Mock.x, fOfA)
                            , (ElemVar Mock.m, Mock.builtinMap [(Mock.b, fOfB)])
                            ]
                        }
                    ]
            actual <-
                unify
                    (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
                    (Mock.concatMap
                        (mkElemVar Mock.m)
                        (Mock.builtinMap [(Mock.a, mkElemVar Mock.x)])
                    )
            assertEqual "" expect actual

        , testCase "framed Map with concrete Map" $ do
            let expect = Just
                    [ Conditional
                        { term =
                            Mock.builtinMap [(Mock.a, fOfA) , (Mock.b, fOfB)]
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap
                            [ (ElemVar Mock.x, fOfA)
                            , (ElemVar Mock.m, Mock.builtinMap [(Mock.b, fOfB)])
                            ]
                        }
                    ]
            actual <-
                unify
                    (Mock.concatMap
                        (Mock.builtinMap [(Mock.a, mkElemVar Mock.x)])
                        (mkElemVar Mock.m)
                    )
                    (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
            assertEqual "" expect actual

        , testCase "framed Map with concrete Map" $ do
            let expect = Just
                    [ Conditional
                        { term =
                            Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)]
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap
                            [ (ElemVar Mock.x, fOfA)
                            , (ElemVar Mock.m, Mock.builtinMap [(Mock.b, fOfB)])
                            ]
                        }
                    ]
            actual <-
                unify
                    (Mock.concatMap
                        (mkElemVar Mock.m)
                        (Mock.builtinMap [(Mock.a, mkElemVar Mock.x)])
                    )
                    (Mock.builtinMap [(Mock.a, fOfA), (Mock.b, fOfB)])
            assertEqual "" expect actual

        , testCase "concrete Map with element+unit" $ do
            let expect = Just
                    [ Conditional
                        { term = Mock.builtinMap [ (Mock.a, fOfA) ]
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap
                            [ (ElemVar Mock.x, Mock.a)
                            , (ElemVar Mock.y, fOfA)
                            ]
                        }
                    ]
            actual <-
                unify
                    (Mock.builtinMap [ (Mock.a, fOfA) ])
                    (Mock.concatMap
                        (Mock.elementMap (mkElemVar Mock.x) (mkElemVar Mock.y))
                        Mock.unitMap
                    )
            assertEqual "" expect actual
        , testCase "map elem key inj splitting" $ do
            let
                expected = Just
                    [ Conditional
                        { term = Mock.builtinMap
                            [   ( Mock.sortInjection Mock.testSort
                                    Mock.aSubSubsort
                                , fOfA
                                )
                            ]
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [   ( ElemVar Mock.xSubSort
                                , Mock.sortInjectionSubSubToSub Mock.aSubSubsort
                                )
                            ,   ( ElemVar Mock.y, fOfA )
                            ]
                        }
                    ]
            actual <- unify
                (Mock.builtinMap
                    [   ( Mock.sortInjection Mock.testSort Mock.aSubSubsort
                        , fOfA
                        )
                    ]
                )
                (Mock.elementMap
                    (Mock.sortInjection Mock.testSort (mkElemVar Mock.xSubSort))
                    (mkElemVar Mock.y)
                )
            assertEqual "" expected actual
        , testCase "map elem value inj splitting" $ do
            let
                key = Mock.a
                value = Mock.sortInjection Mock.testSort Mock.aSubSubsort
                testMap = Mock.builtinMap [(key, value)]
                valueInj = Mock.sortInjection Mock.testSort Mock.aSubSubsort
                testMapInj = Mock.builtinMap [(key, valueInj)]
                expected = Just
                    [ Conditional
                        { term = testMapInj
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [   ( ElemVar Mock.xSubSort
                                , Mock.sortInjection
                                    Mock.subSort
                                    Mock.aSubSubsort
                                )
                            ,   ( ElemVar Mock.y, Mock.a )
                            ]
                        }
                    ]
            actual <- unify
                testMap
                (Mock.elementMap
                    (mkElemVar Mock.y)
                    (Mock.sortInjection Mock.testSort (mkElemVar Mock.xSubSort))
                )
            assertEqual "" expected actual
        , testCase "map concat key inj splitting" $ do
            let
                expected = Just
                    [ Conditional
                        { term = Mock.builtinMap
                            [   ( Mock.sortInjection Mock.testSort
                                    Mock.aSubSubsort
                                , fOfA
                                )
                            ]
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [   ( ElemVar Mock.xSubSort
                                , Mock.sortInjectionSubSubToSub Mock.aSubSubsort
                                )
                            ,   ( ElemVar Mock.y, fOfA )
                            ,   ( ElemVar Mock.m, Mock.builtinMap [])
                            ]
                        }
                    ]
            actual <- unify
                (Mock.builtinMap
                    [   ( Mock.sortInjection Mock.testSort Mock.aSubSubsort
                        , fOfA
                        )
                    ]
                )
                (Mock.concatMap
                    (Mock.elementMap
                        (Mock.sortInjection Mock.testSort (mkElemVar Mock.xSubSort))
                        (mkElemVar Mock.y)
                    )
                    (mkElemVar Mock.m)
                )
            assertEqual "" expected actual
        , testCase "map elem value inj splitting" $ do
            let
                expected = Just
                    [ Conditional
                        { term = Mock.builtinMap
                            [   ( Mock.a
                                , Mock.sortInjection Mock.testSort
                                    Mock.aSubSubsort
                                )
                            ]
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [   ( ElemVar Mock.xSubSort
                                , Mock.sortInjectionSubSubToSub Mock.aSubSubsort
                                )
                            ,   ( ElemVar Mock.y, Mock.a )
                            ,   ( ElemVar Mock.m, Mock.builtinMap [])
                            ]
                        }
                    ]
            actual <- unify
                (Mock.builtinMap
                    [   ( Mock.a
                        , Mock.sortInjection Mock.testSort Mock.aSubSubsort
                        )
                    ]
                )
                (Mock.concatMap
                    (Mock.elementMap
                        (mkElemVar Mock.y)
                        (Mock.sortInjection Mock.testSort (mkElemVar Mock.xSubSort))
                    )
                    (mkElemVar Mock.m)
                )
            assertEqual "" expected actual
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
            actual <- unify term1 term1
            assertEqual "" expect actual

        , testCase "[same head, different head]" $ do
            let term3 = Mock.builtinList [Mock.a, Mock.a]
                term4 = Mock.builtinList [Mock.a, Mock.b]
                expect = Just []
            actual <- unify term3 term4
            assertEqual "" expect actual

        , testCase "[a] `concat` x /\\ [a, b] " $ do
            let x = elemVarS "x" Mock.listSort
                term5 =
                    Mock.concatList (Mock.builtinList [Mock.a]) (mkElemVar x)
                term6 = Mock.builtinList [Mock.a, Mock.b]
                expect = Just
                    [ Conditional
                        { term = Mock.builtinList [Mock.a, Mock.b]
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [(ElemVar x, Mock.builtinList [Mock.b])]
                        }
                    ]
            actual <- unify term5 term6
            assertEqual "" expect actual

        , testCase "different lengths" $ do
            let term7 = Mock.builtinList [Mock.a, Mock.a]
                term8 = Mock.builtinList [Mock.a]
                expect = Just [Pattern.bottom]
            actual <- unify term7 term8
            assertEqual "" expect actual

        , testCase "fallback for external List symbols" $ do
            let expectTerm = mkAnd rhs lhs
                expect =
                    Pattern.fromTermLike expectTerm
                    `Conditional.andPredicate` makeCeilPredicate expectTerm
                x = mkElemVar $ elemVarS "x" Mock.testSort
                l = mkElemVar $ elemVarS "y" Mock.listSort
                -- List unification does not fully succeed because the
                -- elementList symbol is not simplified to a builtin structure.
                lhs = Mock.concatList (Mock.elementList x) l
                rhs = Mock.builtinList [Mock.a, Mock.b]
            actual <- unify lhs rhs
            assertEqual "" (Just [expect]) actual

        -- TODO: Add tests with non-trivial unifications and predicates.
        ]

    , testGroup "Builtin Set domain"
        [ testCase "set singleton + unit" $ do
            let
                expected = Just
                    [ Conditional
                        { term = Mock.builtinSet [Mock.a]
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (ElemVar Mock.x, Mock.a) ]
                        }
                    ]
            actual <- unify
                (Mock.concatSet
                    (Mock.elementSet (mkElemVar Mock.x))
                    Mock.unitSet
                )
                (Mock.builtinSet [Mock.a])
            assertEqual "" expected actual
        ,  testCase "handles set ambiguity" $ do
            let
                expected1 =
                    Conditional
                        { term = Mock.builtinSet [Mock.a, Mock.b]
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (ElemVar Mock.x, Mock.a)
                            , (ElemVar Mock.xSet, Mock.builtinSet [Mock.b])
                            ]
                        }
                expected2 =
                    Conditional
                        { term = Mock.builtinSet [Mock.a, Mock.b]
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (ElemVar Mock.x, Mock.b)
                            , (ElemVar Mock.xSet, Mock.builtinSet [Mock.a])
                            ]
                        }
            actual <- unify
                (Mock.concatSet
                    (Mock.elementSet (mkElemVar Mock.x))
                    (mkElemVar Mock.xSet)
                )
                (Mock.builtinSet [Mock.a, Mock.b])
            assertEqual "" (Just [expected1, expected2]) actual
        , testCase "set elem inj splitting" $ do
            let
                expected = Just
                    [ Conditional
                        { term = Mock.builtinSet
                            [ Mock.sortInjection Mock.testSort Mock.aSubSubsort ]
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [   ( ElemVar Mock.xSubSort
                                , Mock.sortInjectionSubSubToSub Mock.aSubSubsort
                                )
                            ]
                        }
                    ]
            actual <- unify
                (Mock.elementSet
                    (Mock.sortInjection Mock.testSort (mkElemVar Mock.xSubSort))
                )
                (Mock.builtinSet
                    [Mock.sortInjection Mock.testSort Mock.aSubSubsort]
                )
            assertEqual "" expected actual
        , testCase "set concat inj splitting" $ do
            let
                expected = Just
                    [ Conditional
                        { term = Mock.builtinSet
                            [ Mock.sortInjection Mock.testSort Mock.aSubSubsort ]
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [   ( ElemVar Mock.xSubSort
                                , Mock.sortInjectionSubSubToSub Mock.aSubSubsort
                                )
                            ,   ( ElemVar Mock.xSet
                                , Mock.builtinSet []
                                )
                            ]
                        }
                    ]
            actual <- unify
                (Mock.concatSet
                    (Mock.elementSet
                        (Mock.sortInjection Mock.testSort (mkElemVar Mock.xSubSort))
                    )
                    (mkElemVar Mock.xSet)
                )
                (Mock.builtinSet
                    [Mock.sortInjection Mock.testSort Mock.aSubSubsort]
                )
            assertEqual "" expected actual
        , testCase "set concat 2 inj splitting" $ do
            let
                testSet =
                    Mock.builtinSet
                        [ Mock.a
                        , Mock.sortInjection Mock.testSort Mock.aSubSubsort
                        ]
                expected =
                    [ Conditional
                            { term = testSet
                            , predicate = makeTruePredicate
                            , substitution = Substitution.unsafeWrap
                                [   (ElemVar Mock.x, Mock.a)
                                ,   ( ElemVar Mock.xSubSort
                                    , Mock.sortInjectionSubSubToSub
                                        Mock.aSubSubsort
                                    )
                                ,   (ElemVar Mock.xSet, Mock.builtinSet [])
                                ]
                            }
                    ]
            actual <- unify
                (Mock.concatSet
                    (Mock.elementSet (mkElemVar Mock.x))
                    (Mock.concatSet
                        (Mock.elementSet
                            (Mock.sortInjection
                                Mock.testSort
                                (mkElemVar Mock.xSubSort)
                            )
                        )
                        (mkElemVar Mock.xSet)
                    )
                )
                testSet
            assertEqual "" (Just expected) actual
        ]
    , testGroup "alias expansion"
        [ testCase "alias() vs top" $ do
            let
                x = mkVariable "x"
                alias = mkAlias' "alias1" x mkTop_
                left = applyAlias' alias $ mkTop Mock.testSort
            actual <- simplifyUnify left mkTop_
            assertExpectTop actual
        , testCase "alias1() vs alias2()" $ do
            let
                x = mkVariable "x"
                leftAlias = mkAlias' "leftAlias" x mkTop_
                left = applyAlias' leftAlias $ mkTop Mock.testSort
                rightAlias = mkAlias' "rightAlias" x mkTop_
                right = applyAlias' rightAlias $ mkTop Mock.testSort
            actual <- simplifyUnify left right
            assertExpectTop actual
        , testCase "alias1(alias2()) vs top" $ do
            let
                x = mkVariable "x"
                y = mkVariable "y"
                alias1 = mkAlias' "alias1" x mkTop_
                alias1App = applyAlias' alias1 $ mkSetVar (SetVariable y)
                alias2 = mkAlias' "alias2" x alias1App
                alias2App = applyAlias' alias2 $ mkTop Mock.testSort
            actual <- simplifyUnify alias2App mkTop_
            assertExpectTop actual
        , testCase "alias1() vs injHead" $ do
            let
                expect =
                    Conditional
                        { term = Mock.injective10 fOfA
                        , predicate = makeEqualsPredicate fOfA gOfA
                        , substitution = mempty
                        }
                x = mkVariable "x"
                alias = mkAlias' "alias1" x $ Mock.injective10 fOfA
                left = applyAlias' alias $ mkTop Mock.testSort
            actual <- simplifyUnify left $ Mock.injective10 gOfA
            assertEqual "" ([expect], Just [expect]) actual
        , testGroup "unhandled cases with aliases"
            [ testCase "top level" $ do
                let
                    expect =
                        (   [ Conditional
                                { term = mkAnd left plain1OfA
                                , predicate = makeTruePredicate
                                , substitution = mempty
                                }
                            ]
                        , Nothing
                        )
                    x = mkVariable "x"
                    alias = mkAlias' "alias1" x $ plain0OfA
                    left = applyAlias' alias $ mkTop Mock.testSort
                actual <- simplifyUnify left plain1OfA
                assertEqual "" expect actual

            , testCase "one level deep" $ do
                let
                    expect =
                        (   [ Conditional
                                { term = Mock.constr10 (mkAnd plain0OfA plain1OfA)
                                , predicate = makeTruePredicate
                                , substitution = mempty
                                }
                            ]
                        , Nothing
                        )
                    x = mkVariable "x"
                    alias = mkAlias' "alias1" x $ Mock.constr10 plain0OfA
                    left = applyAlias' alias $ mkTop Mock.testSort
                actual <- simplifyUnify left $ Mock.constr10 plain1OfA
                assertEqual "" expect actual
            ]
        ]
    ]

mkVariable :: Text -> Variable
mkVariable ident = Variable (testId ident) Nothing Mock.testSort

mkAlias' :: Text -> Variable -> TermLike Variable -> SentenceAlias (TermLike Variable)
mkAlias' ident var inner =
    mkAlias_ (testId ident) Mock.testSort [SetVar $ SetVariable var] inner

applyAlias'
    :: Ord variable
    => SortedVariable variable
    => Unparse variable
    => SentenceAlias (TermLike Variable)
    -> TermLike variable
    -> TermLike variable
applyAlias' alias arg = applyAlias alias [] [arg]

assertExpectTop :: ([Pattern Variable], Maybe [Pattern Variable]) -> IO ()
assertExpectTop =
    assertEqual "" ([Pattern.top], Just [Pattern.top])

test_equalsTermsSimplification :: [TestTree]
test_equalsTermsSimplification =
    [ testCase "adds ceil when producing substitutions" $ do
        let expected = Just
                [ Conditional
                    { term = ()
                    , predicate = makeCeilPredicate Mock.cf
                    , substitution =
                        Substitution.unsafeWrap [(ElemVar Mock.x, Mock.cf)]
                    }
                ]
        actual <- simplifyEquals Map.empty (mkElemVar Mock.x) Mock.cf
        assertEqual "" expected actual
    , testCase "handles ambiguity" $ do
        let
            expected = Just
                [ Conditional
                    { term = ()
                    , predicate = makeEqualsPredicate (Mock.f Mock.a) Mock.a
                    , substitution =
                        Substitution.unsafeWrap [(ElemVar Mock.x, Mock.cf)]
                    }
                , Conditional
                    { term = ()
                    , predicate = makeEqualsPredicate (Mock.f Mock.b) Mock.b
                    , substitution =
                        Substitution.unsafeWrap [(ElemVar Mock.x, Mock.cf)]
                    }
                ]
            sortVar = SortVariableSort (SortVariable (testId "S"))
            simplifiers = axiomPatternsToEvaluators $ Map.fromList
                [   (   AxiomIdentifier.Ceil
                            (AxiomIdentifier.Application Mock.cfId)
                    ,   [ EqualityRule RulePattern
                            { left = mkCeil sortVar Mock.cf
                            , antiLeft = Nothing
                            , right =
                                mkOr
                                    (mkAnd
                                        (mkEquals_
                                            (Mock.f (mkElemVar Mock.y))
                                            Mock.a
                                        )
                                        (mkEquals_ (mkElemVar Mock.y) Mock.a)
                                    )
                                    (mkAnd
                                        (mkEquals_
                                            (Mock.f (mkElemVar Mock.y))
                                            Mock.b
                                        )
                                        (mkEquals_ (mkElemVar Mock.y) Mock.b)
                                    )
                            , requires = makeTruePredicate
                            , ensures = makeTruePredicate
                            , attributes = def
                                {Attribute.simplification = Simplification True}
                            }
                        ]
                    )
                ]
        actual <- simplifyEquals simplifiers (mkElemVar Mock.x) Mock.cf
        assertEqual "" expected actual
    , testCase "handles multiple ambiguity" $ do
        let
            expected = Just
                [ Conditional
                    { term = ()
                    , predicate = makeAndPredicate
                        (makeEqualsPredicate (Mock.f Mock.a) Mock.a)
                        (makeEqualsPredicate (Mock.g Mock.a) Mock.a)
                    , substitution = Substitution.unsafeWrap
                        [ (ElemVar Mock.x, Mock.cf)
                        , (ElemVar Mock.var_x_1, Mock.cg)
                        ]
                    }
                , Conditional
                    { term = ()
                    , predicate = makeAndPredicate
                        (makeEqualsPredicate (Mock.f Mock.a) Mock.a)
                        (makeEqualsPredicate (Mock.g Mock.b) Mock.b)
                    , substitution = Substitution.unsafeWrap
                        [ (ElemVar Mock.x, Mock.cf)
                        , (ElemVar Mock.var_x_1, Mock.cg)
                        ]
                    }
                , Conditional
                    { term = ()
                    , predicate = makeAndPredicate
                        (makeEqualsPredicate (Mock.f Mock.b) Mock.b)
                        (makeEqualsPredicate (Mock.g Mock.a) Mock.a)
                    , substitution = Substitution.unsafeWrap
                        [ (ElemVar Mock.x, Mock.cf)
                        , (ElemVar Mock.var_x_1, Mock.cg)
                        ]
                    }
                , Conditional
                    { term = ()
                    , predicate = makeAndPredicate
                        (makeEqualsPredicate (Mock.f Mock.b) Mock.b)
                        (makeEqualsPredicate (Mock.g Mock.b) Mock.b)
                    , substitution = Substitution.unsafeWrap
                        [ (ElemVar Mock.x, Mock.cf)
                        , (ElemVar Mock.var_x_1, Mock.cg)
                        ]
                    }
                ]
            sortVar = SortVariableSort (SortVariable (testId "S"))
            simplifiers = axiomPatternsToEvaluators $ Map.fromList
                [   (   AxiomIdentifier.Ceil
                            (AxiomIdentifier.Application Mock.cfId)
                    ,   [ EqualityRule RulePattern
                            { left = mkCeil sortVar Mock.cf
                            , antiLeft = Nothing
                            , right =
                                mkOr
                                    (mkAnd
                                        (mkEquals_
                                            (Mock.f (mkElemVar Mock.y))
                                            Mock.a
                                        )
                                        (mkEquals_ (mkElemVar Mock.y) Mock.a)
                                    )
                                    (mkAnd
                                        (mkEquals_
                                            (Mock.f (mkElemVar Mock.y))
                                            Mock.b
                                        )
                                        (mkEquals_ (mkElemVar Mock.y) Mock.b)
                                    )
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
                            , antiLeft = Nothing
                            , right =
                                mkOr
                                    (mkAnd
                                        (mkEquals_
                                            (Mock.g (mkElemVar Mock.z))
                                            Mock.a
                                        )
                                        (mkEquals_ (mkElemVar Mock.z) Mock.a)
                                    )
                                    (mkAnd
                                        (mkEquals_
                                            (Mock.g (mkElemVar Mock.z))
                                            Mock.b
                                        )
                                        (mkEquals_ (mkElemVar Mock.z) Mock.b)
                                    )
                            , requires = makeTruePredicate
                            , ensures = makeTruePredicate
                            , attributes = def
                                {Attribute.simplification = Simplification True}
                            }
                        ]
                    )
                ]
        actual <- simplifyEquals
            simplifiers
            (Mock.functionalConstr20 (mkElemVar Mock.x) (mkElemVar Mock.var_x_1))
            (Mock.functionalConstr20 Mock.cf Mock.cg)
        assertEqual "" expected actual
    , testCase "handles set ambiguity" $ do
        let
            asInternal set =
                Ac.asInternalConcrete
                    Mock.metadataTools
                    Mock.setSort
                    (Map.fromSet (const Domain.SetValue) set)
            expected = Just $ do -- list monad
                (xValue, xSetValue) <-
                    [ (Mock.a, [Mock.b])
                    , (Mock.b, [Mock.a])
                    ]
                return Conditional
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [ (ElemVar Mock.x, xValue)
                        , ( ElemVar Mock.xSet
                          , asInternal (Set.fromList xSetValue)
                          )
                        ]
                    }
        actual <- simplifyEquals
            Map.empty
            (Mock.concatSet (Mock.elementSet (mkElemVar Mock.x)) (mkElemVar Mock.xSet))
            (asInternal (Set.fromList [Mock.a, Mock.b]))
        assertEqual "" expected actual
    ]

test_functionAnd :: [TestTree]
test_functionAnd =
    [ testCase "simplifies result" $ do
        let f = TermLike.markSimplified . Mock.f
            x = mkElemVar Mock.x
            y = mkElemVar Mock.y
            expect =
                Pattern.withCondition (f x)
                $ Predicate.fromPredicate
                $ makeEqualsPredicate (f x) (f y)
        let Just actual = functionAnd (f x) (f y)
        assertEqual "" expect actual
        assertBool "" (Pattern.isSimplified actual)
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
    mkDomainValue DomainValue
        { domainValueSort = Mock.testSort
        , domainValueChild = mkStringLiteral "a"
        }

bDomainValue :: TermLike Variable
bDomainValue =
    mkDomainValue DomainValue
        { domainValueSort = Mock.testSort
        , domainValueChild = mkStringLiteral "b"
        }

simplifyUnify
    :: TermLike Variable
    -> TermLike Variable
    -> IO ([Pattern Variable], Maybe [Pattern Variable])
simplifyUnify first second =
    (,)
        <$> simplify first second
        <*> unify first second

unify
    :: TermLike Variable
    -> TermLike Variable
    -> IO (Maybe [Pattern Variable])
unify first second =
    runSimplifier mockEnv $ runMaybeT unification
  where
    mockEnv = Mock.env
    unification =
        -- The unification error is discarded because, for testing purposes, we
        -- are not interested in the /reason/ unification failed. For the tests,
        -- the failure is almost always due to unsupported patterns anyway.
        MaybeT . fmap Error.hush . Monad.Unify.runUnifierT
        $ termUnification first second

simplify
    :: TermLike Variable
    -> TermLike Variable
    -> IO [Pattern Variable]
simplify first second =
    runSimplifierBranch mockEnv $ termAnd first second
  where
    mockEnv = Mock.env

simplifyEquals
    :: BuiltinAndAxiomSimplifierMap
    -> TermLike Variable
    -> TermLike Variable
    -> IO (Maybe [Predicate Variable])
simplifyEquals simplifierAxioms first second =
    (fmap . fmap) MultiOr.extractPatterns
    $ runSimplifier mockEnv
    $ runMaybeT $ termEquals first second
  where
    mockEnv = Mock.env { simplifierAxioms }
