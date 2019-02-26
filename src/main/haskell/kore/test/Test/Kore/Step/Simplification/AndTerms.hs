module Test.Kore.Step.Simplification.AndTerms
    ( test_andTermsSimplification
    ) where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
       ( testCase )

import           Control.Error
                 ( MaybeT (..) )
import qualified Control.Error as Error

import           Kore.AST.Pure
import           Kore.AST.Valid
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Predicate.Predicate
                 ( makeEqualsPredicate, makeFalsePredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( bottom )
import           Kore.Step.Pattern
import           Kore.Step.Simplification.AndTerms
                 ( termAnd, termUnification )
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Unification.Substitution as Substitution
import qualified SMT

import           Test.Kore
import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools )
import qualified Test.Kore.Step.MockSimplifiers as Mock
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_andTermsSimplification :: [TestTree]
test_andTermsSimplification =
    [ testGroup "Predicates"
        [ testCase "\\and{s}(f{}(a), \\top{s}())" $ do
            let expected =
                    Predicated
                        { term = fOfA
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            actual <- simplifyUnify mockMetadataTools fOfA mkTop_
            assertEqualWithExplanation "" (expected, Just expected) actual

        , testCase "\\and{s}(\\top{s}(), f{}(a))" $ do
            let expected =
                    Predicated
                        { term = fOfA
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            actual <- simplifyUnify mockMetadataTools mkTop_ fOfA
            assertEqualWithExplanation "" (expected, Just expected) actual

        , testCase "\\and{s}(f{}(a), \\bottom{s}())" $ do
            let expect =
                    ( ExpandedPattern.bottom
                    , Just ExpandedPattern.bottom
                    )
            actual <- simplifyUnify mockMetadataTools fOfA mkBottom_
            assertEqualWithExplanation "" expect actual

        , testCase "\\and{s}(\\bottom{s}(), f{}(a))" $ do
            let expect =
                    ( ExpandedPattern.bottom
                    , Just ExpandedPattern.bottom
                    )
            actual <-
                simplifyUnify
                    mockMetadataTools
                    mkBottom_
                    fOfA
            assertEqualWithExplanation "" expect actual
        ]

    , testCase "equal patterns and" $ do
        let expect =
                Predicated
                    { term = fOfA
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            simplifyUnify
                mockMetadataTools
                fOfA fOfA
        assertEqualWithExplanation "" (expect, Just expect) actual

    , testGroup "variable function and"
        [ testCase "\\and{s}(x:s, f{}(a))" $ do
            let expect =
                    Predicated
                        { term = fOfA
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap [(Mock.x, fOfA)]
                        }
            actual <-
                simplifyUnify
                    mockMetadataTools
                    (mkVar Mock.x) fOfA
            assertEqualWithExplanation "" (expect, Just expect) actual

        , testCase "\\and{s}(f{}(a), x:s)" $ do
            let expect =
                    Predicated
                        { term = fOfA
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap [(Mock.x, fOfA)]
                        }
            actual <-
                simplifyUnify
                    mockMetadataTools
                    fOfA (mkVar Mock.x)
            assertEqualWithExplanation "" (expect, Just expect) actual
        ]

    , testGroup "injective head and"
        [ testCase "same head, different child" $ do
            let expect =
                    Predicated
                        { term = Mock.injective10 fOfA
                        , predicate = makeEqualsPredicate fOfA gOfA
                        , substitution = mempty
                        }
            actual <-
                simplifyUnify
                    mockMetadataTools
                    (Mock.injective10 fOfA) (Mock.injective10 gOfA)
            assertEqualWithExplanation "" (expect, Just expect) actual
        , testCase "same head, same child" $ do
            let expected =
                    Predicated
                        { term = Mock.injective10 fOfA
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            actual <-
                simplifyUnify
                    mockMetadataTools
                    (Mock.injective10 fOfA) (Mock.injective10 fOfA)
            assertEqualWithExplanation "" (expected, Just expected) actual
        , testCase "different head" $ do
            let expect =
                    ( Predicated
                        { term =
                            mkAnd
                                (Mock.injective10 fOfA)
                                (Mock.injective11 gOfA)
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    , Nothing
                    )
            actual <-
                simplifyUnify
                    mockMetadataTools
                    (Mock.injective10 fOfA) (Mock.injective11 gOfA)
            assertEqualWithExplanation "" expect actual
        ]

    , testGroup "sort injection and"
        [ testCase "same head, different child" $ do
            let expect =
                    Predicated
                        { term = Mock.sortInjection10 Mock.cfSort0
                        , predicate =
                            makeEqualsPredicate Mock.cfSort0 Mock.cgSort0
                        , substitution = mempty
                        }
            actual <-
                simplifyUnify
                    mockMetadataTools
                    (Mock.sortInjection10 Mock.cfSort0)
                    (Mock.sortInjection10 Mock.cgSort0)
            assertEqualWithExplanation "" (expect, Just expect) actual
        , testCase "same head, same child" $ do
            let expect =
                    Predicated
                        { term =
                            Mock.sortInjection10 Mock.cfSort0
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            actual <-
                simplifyUnify
                    mockMetadataTools
                    (Mock.sortInjection10 Mock.cfSort0)
                    (Mock.sortInjection10 Mock.cfSort0)
            assertEqualWithExplanation "" (expect, Just expect) actual
        , testCase "different head, not subsort" $ do
            let expect =
                    (ExpandedPattern.bottom, Just ExpandedPattern.bottom)
            actual <-
                simplifyUnify
                    mockMetadataTools
                    (Mock.sortInjectionSubToTop Mock.plain00Subsort)
                    (Mock.sortInjection0ToTop Mock.plain00Sort0)
            assertEqualWithExplanation "" expect actual
        , testCase "different head, subsort first" $ do
            let expect =
                    ( Predicated
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
                    , Nothing
                    )
            actual <-
                simplifyUnify
                    mockMetadataTools
                    (Mock.sortInjectionSubSubToTop Mock.plain00SubSubsort)
                    (Mock.sortInjectionSubToTop Mock.plain00Subsort)
            assertEqualWithExplanation "" expect actual
        , testCase "different head, subsort second" $ do
            let expect =
                    ( Predicated
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
                    , Nothing
                    )
            actual <-
                simplifyUnify
                    mockMetadataTools
                    (Mock.sortInjectionSubToTop Mock.plain00Subsort)
                    (Mock.sortInjectionSubSubToTop Mock.plain00SubSubsort)
            assertEqualWithExplanation "" expect actual
        , testCase "different head constructors not subsort" $ do
            let expect =
                    ( ExpandedPattern.bottom
                    , Just ExpandedPattern.bottom
                    )
            actual <-
                simplifyUnify
                    mockMetadataTools
                    (Mock.sortInjection10 Mock.aSort0)
                    (Mock.sortInjection11 Mock.aSort1)
            assertEqualWithExplanation "" expect actual
        , testCase "different head constructors subsort" $ do
            let expect =
                    ( ExpandedPattern.bottom
                    , Just ExpandedPattern.bottom
                    )
            actual <-
                simplifyUnify
                    mockMetadataTools
                    (Mock.sortInjectionSubToTop Mock.aSubsort)
                    (Mock.sortInjectionSubSubToTop Mock.aSubSubsort)
            assertEqualWithExplanation "" expect actual
        , testCase "different head constructors common subsort" $ do
            let expect =
                    ( ExpandedPattern.bottom
                    , Just ExpandedPattern.bottom
                    )
            actual <-
                simplifyUnify
                    mockMetadataTools
                    (Mock.sortInjectionOtherToTop Mock.aOtherSort)
                    (Mock.sortInjectionSubToTop Mock.aSubsort)
            assertEqualWithExplanation "" expect actual
        , testCase "different head constructors common subsort reversed" $ do
            let expect =
                    ( ExpandedPattern.bottom
                    , Just ExpandedPattern.bottom
                    )
            actual <-
                simplifyUnify
                    mockMetadataTools
                    (Mock.sortInjectionSubToTop Mock.aSubsort)
                    (Mock.sortInjectionOtherToTop Mock.aOtherSort)
            assertEqualWithExplanation "" expect actual
        ]

    , testGroup "constructor and"
        [ testCase "same head" $ do
            let expect =
                    let
                        expected = Predicated
                            { term = Mock.constr10 Mock.cf
                            , predicate = makeEqualsPredicate Mock.cf Mock.cg
                            , substitution = mempty
                            }
                    in (expected, Just expected)
            actual <-
                simplifyUnify
                    mockMetadataTools
                    (Mock.constr10 Mock.cf)
                    (Mock.constr10 Mock.cg)
            assertEqualWithExplanation "" expect actual

        , testCase "same head same child" $ do
            let expect =
                    let
                        expected = Predicated
                            { term = Mock.constr10 Mock.cf
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                    in (expected, Just expected)
            actual <-
                simplifyUnify
                    mockMetadataTools
                    (Mock.constr10 Mock.cf)
                    (Mock.constr10 Mock.cf)
            assertEqualWithExplanation "" expect actual

        , testCase "different head" $ do
            let expect =
                    ( ExpandedPattern.bottom
                    , Just ExpandedPattern.bottom
                    )
            actual <-
                simplifyUnify
                    mockMetadataTools
                    (Mock.constr10 Mock.cf)
                    (Mock.constr11 Mock.cf)
            assertEqualWithExplanation "" expect actual
        ]

    , testCase "constructor-sortinjection and" $ do
        let expect =
                ( ExpandedPattern.bottom
                , Just ExpandedPattern.bottom
                )
        actual <-
            simplifyUnify
                mockMetadataTools
                (Mock.constr10 Mock.cf)
                (Mock.sortInjection11 Mock.cfSort1)
        assertEqualWithExplanation "" expect actual

    , testGroup "domain value and"
        [ testCase "equal values" $ do
            let expect =
                    let
                        expected = Predicated
                            { term = aDomainValue
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                    in (expected, Just expected)
            actual <-
                simplifyUnify
                    mockMetadataTools
                    aDomainValue aDomainValue
            assertEqualWithExplanation "" expect actual

        , testCase "different values" $ do
            let expect =
                    ( ExpandedPattern.bottom
                    , Just ExpandedPattern.bottom
                    )
            actual <-
                simplifyUnify
                    mockMetadataTools
                    aDomainValue bDomainValue
            assertEqualWithExplanation "" expect actual
        ]

    , testGroup "string literal and"
        [ testCase "equal values" $ do
            let expect =
                    let
                        expected = Predicated
                            { term = mkStringLiteral "a"
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                    in (expected, Just expected)
            actual <-
                simplifyUnify
                    mockMetaMetadataTools
                    (mkStringLiteral "a")
                    (mkStringLiteral "a")
            assertEqualWithExplanation "" expect actual

        , testCase "different values" $ do
            let expect =
                    ( ExpandedPattern.bottom
                    , Just ExpandedPattern.bottom
                    )
            actual <-
                simplifyUnify
                    mockMetaMetadataTools
                    (mkStringLiteral "a")
                    (mkStringLiteral "b")
            assertEqualWithExplanation "" expect actual
        ]

    , testGroup "char literal and"
        [ testCase "equal values" $ do
            let expect =
                    let
                        expected = Predicated
                            { term = mkCharLiteral 'a'
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                    in (expected, Just expected)
            actual <-
                simplifyUnify
                    mockMetaMetadataTools
                    (mkCharLiteral 'a')
                    (mkCharLiteral 'a')
            assertEqualWithExplanation "" expect actual

        , testCase "different values" $ do
            let expect =
                    ( ExpandedPattern.bottom
                    , Just ExpandedPattern.bottom
                    )
            actual <-
                simplifyUnify
                    mockMetaMetadataTools
                    (mkCharLiteral 'a')
                    (mkCharLiteral 'b')
            assertEqualWithExplanation "" expect actual
        ]

    , testGroup "function and"
        [ testCase "equal values" $ do
            let expect =
                    let
                        expanded = Predicated
                            { term = fOfA
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                    in (expanded, Just expanded)
            actual <-
                simplifyUnify
                    mockMetadataTools
                    fOfA fOfA
            assertEqualWithExplanation "" expect actual

        , testCase "not equal values" $ do
            let expect =
                    let
                        expanded = Predicated
                            { term = fOfA
                            , predicate = makeEqualsPredicate fOfA gOfA
                            , substitution = mempty
                            }
                    in (expanded, Just expanded)
            actual <-
                simplifyUnify
                    mockMetadataTools
                    fOfA gOfA
            assertEqualWithExplanation "" expect actual
        ]

    , testGroup "unhandled cases"
        [ testCase "top level" $ do
            let expect =
                    ( Predicated
                        { term = mkAnd plain0OfA plain1OfA
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    , Nothing
                    )
            actual <-
                simplifyUnify
                    mockMetadataTools
                    plain0OfA plain1OfA
            assertEqualWithExplanation "" expect actual

        , testCase "one level deep" $ do
            let expect =
                    ( Predicated
                        { term = Mock.constr10 (mkAnd plain0OfA plain1OfA)
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    , Nothing
                    )
            actual <-
                simplifyUnify
                    mockMetadataTools
                    (Mock.constr10 plain0OfA) (Mock.constr10 plain1OfA)
            assertEqualWithExplanation "" expect actual

        , testCase "two levels deep" $ do
            let expect =
                    ( Predicated
                        { term =
                            Mock.constr10
                                (Mock.constr10 (mkAnd plain0OfA plain1OfA))
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    , Nothing
                    )
            actual <-
                simplifyUnify
                    mockMetadataTools
                    (Mock.constr10 (Mock.constr10 plain0OfA))
                    (Mock.constr10 (Mock.constr10 plain1OfA))
            assertEqualWithExplanation "" expect actual
        ]

    , testCase "binary constructor of non-specialcased values" $ do
        let expect =
                ( Predicated
                    { term =
                        Mock.functionalConstr20
                            (mkAnd plain0OfA plain1OfA)
                            (mkAnd plain0OfB plain1OfB)
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                , Nothing
                )
        actual <-
            simplifyUnify
                mockMetadataTools
                (Mock.functionalConstr20 plain0OfA plain0OfB)
                (Mock.functionalConstr20 plain1OfA plain1OfB)
        assertEqualWithExplanation "" expect actual

    , testGroup "builtin Map domain"
        [ testCase "concrete Map, same keys" $ do
            let expect =
                    Just Predicated
                        { term = Mock.builtinMap [(Mock.aConcrete, Mock.b)]
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap [(Mock.x, Mock.b)]
                        }
            actual <-
                unify
                    mockMetadataTools
                    (Mock.builtinMap [(Mock.aConcrete, Mock.b)])
                    (Mock.builtinMap [(Mock.aConcrete, mkVar Mock.x)])
            assertEqualWithExplanation "" expect actual

        , testCase "concrete Map, different keys" $ do
            let expect = Just ExpandedPattern.bottom
            actual <-
                unify
                    mockMetadataTools
                    (Mock.builtinMap [(Mock.aConcrete, Mock.b)])
                    (Mock.builtinMap [(Mock.bConcrete, mkVar Mock.x)])
            assertEqualWithExplanation "" expect actual

        , testCase "concrete Map with framed Map" $ do
            let expect =
                    Just Predicated
                        { term =
                            Mock.builtinMap
                                [ (Mock.aConcrete, fOfA)
                                , (Mock.bConcrete, fOfB)
                                ]
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.m, Mock.builtinMap [(Mock.bConcrete, fOfB)])
                            , (Mock.x, fOfA)
                            ]
                        }
            actual <-
                unify
                    mockMetadataTools
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
            let expect =
                    Just Predicated
                        { term =
                            Mock.builtinMap
                                [ (Mock.aConcrete, fOfA)
                                , (Mock.bConcrete, fOfB)
                                ]
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.m, Mock.builtinMap [(Mock.bConcrete, fOfB)])
                            , (Mock.x, fOfA)
                            ]
                        }
            actual <-
                unify
                    mockMetadataTools
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
            let expect =
                    Just Predicated
                        { term =
                            Mock.builtinMap
                                [ (Mock.aConcrete, fOfA)
                                , (Mock.bConcrete, fOfB)
                                ]
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.m, Mock.builtinMap [(Mock.bConcrete, fOfB)])
                            , (Mock.x, fOfA)
                            ]
                        }
            actual <-
                unify
                    mockMetadataTools
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
            let expect =
                    Just Predicated
                        { term =
                            Mock.builtinMap
                                [ (Mock.aConcrete, fOfA)
                                , (Mock.bConcrete, fOfB)
                                ]
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.m, Mock.builtinMap [(Mock.bConcrete, fOfB)])
                            , (Mock.x, fOfA)
                            ]
                        }
            actual <-
                unify
                    mockMetadataTools
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
                expect =
                    Just Predicated
                        { term = term1
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            actual <- unify mockMetadataTools term1 term1
            assertEqualWithExplanation "" expect actual

        , testCase "[same head, different head]" $ do
            let term3 = Mock.builtinList [Mock.a, Mock.a]
                term4 = Mock.builtinList [Mock.a, Mock.b]
                expect =
                    Just Predicated
                        { term = Mock.builtinList [Mock.a, mkBottom_]
                        , predicate = makeFalsePredicate
                        , substitution = mempty
                        }
            actual <- unify mockMetadataTools term3 term4
            assertEqualWithExplanation "" expect actual

        , testCase "[a] `concat` x /\\ [a, b] " $ do
            let term5 = Mock.concatList
                        (Mock.builtinList [Mock.a])
                        (mkVar Mock.x)
                term6 = Mock.builtinList $ [Mock.a, Mock.b]
                expect =
                    Just Predicated
                        { term = Mock.builtinList $ [Mock.a, Mock.b]
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap
                            [(Mock.x, Mock.builtinList [Mock.b])]
                        }
            actual <- unify mockMetadataTools term5 term6
            assertEqualWithExplanation "" expect actual

        , testCase "different lengths" $ do
            let term7 = Mock.builtinList [Mock.a, Mock.a]
                term8 = Mock.builtinList [Mock.a]
                expect = Just ExpandedPattern.bottom
            actual <- unify mockMetadataTools term7 term8
            assertEqualWithExplanation "" expect actual

        -- TODO: Add tests with non-trivial unifications and predicates.
        ]
    -- TODO: Add tests for set unification.
    ]

fOfA :: CommonStepPattern Object
fOfA = Mock.f Mock.a

fOfB :: CommonStepPattern Object
fOfB = Mock.f Mock.b

gOfA :: CommonStepPattern Object
gOfA = Mock.g Mock.a

plain0OfA :: CommonStepPattern Object
plain0OfA = Mock.plain10 Mock.a

plain1OfA :: CommonStepPattern Object
plain1OfA = Mock.plain11 Mock.a

plain0OfB :: CommonStepPattern Object
plain0OfB = Mock.plain10 Mock.b

plain1OfB :: CommonStepPattern Object
plain1OfB = Mock.plain11 Mock.b

mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools
        Mock.attributesMapping
        Mock.headTypeMapping
        Mock.sortAttributesMapping
        Mock.subsorts

mockMetaMetadataTools :: MetadataTools Meta StepperAttributes
mockMetaMetadataTools = Mock.makeMetadataTools [] [] [] []

aDomainValue :: CommonStepPattern Object
aDomainValue =
    mkDomainValue  Mock.testSort
        $ Domain.BuiltinPattern
        $ eraseAnnotations
        $ mkStringLiteral "a"

bDomainValue :: CommonStepPattern Object
bDomainValue =
    mkDomainValue Mock.testSort
        $ Domain.BuiltinPattern
        $ eraseAnnotations
        $ mkStringLiteral "b"

simplifyUnify
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -> CommonStepPattern level
    -> CommonStepPattern level
    -> IO (CommonExpandedPattern level, Maybe (CommonExpandedPattern level))
simplifyUnify tools first second =
    (,)
        <$> simplify tools first second
        <*> unify tools first second


unify
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -> CommonStepPattern level
    -> CommonStepPattern level
    -> IO (Maybe (CommonExpandedPattern level))
unify tools first second =
    SMT.runSMT SMT.defaultConfig
        $ evalSimplifier emptyLogger noRepl
        $ runMaybeT
        $ (<$>) fst
        $ unification
  where
    substitutionSimplifier = Mock.substitutionSimplifier tools
    unification =
        -- The unification error is discarded because, for testing purposes, we
        -- are not interested in the /reason/ unification failed. For the tests,
        -- the failure is almost always due to unsupported patterns anyway.
        Error.hushT $ termUnification tools substitutionSimplifier first second

simplify
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -> CommonStepPattern level
    -> CommonStepPattern level
    -> IO (CommonExpandedPattern level)
simplify tools first second =
    (<$>) fst
    $ SMT.runSMT SMT.defaultConfig
    $ evalSimplifier emptyLogger noRepl
    $ termAnd tools (Mock.substitutionSimplifier tools) first second
