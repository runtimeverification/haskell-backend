module Test.Kore.Step.Simplification.Ceil
    ( test_ceilSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import qualified Data.Map as Map

import qualified Data.Sup as Sup
import           Kore.AST.Pure
import           Kore.AST.Valid
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Logger.Output as Logger
                 ( emptyLogger )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeCeilPredicate, makeEqualsPredicate,
                 makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( bottom, mapVariables, top )
import           Kore.Step.Function.Data
                 ( AttemptedAxiom,
                 AttemptedAxiomResults (AttemptedAxiomResults),
                 BuiltinAndAxiomSimplifier (BuiltinAndAxiomSimplifier),
                 BuiltinAndAxiomSimplifierMap )
import qualified Kore.Step.Function.Data as AttemptedAxiomResults
                 ( AttemptedAxiomResults (..) )
import qualified Kore.Step.Function.Data as AttemptedAxiom
                 ( AttemptedAxiom (..) )
import qualified Kore.Step.Function.Identifier as AxiomIdentifier
                 ( AxiomIdentifier (..) )
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern, OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Pattern
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluate, simplify )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier,
                 SimplificationProof (SimplificationProof), Simplifier,
                 StepPatternSimplifier, evalSimplifier )
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Variables.Fresh
                 ( FreshVariable )
import qualified SMT

import           Test.Kore
                 ( noRepl )
import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools )
import qualified Test.Kore.Step.MockSimplifiers as Mock
import           Test.Kore.Step.MockSymbols
                 ( testSort )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_ceilSimplification :: [TestTree]
test_ceilSimplification =
    [ testCase "Ceil - or distribution" $ do
        -- ceil(a or b) = (top and ceil(a)) or (top and ceil(b))
        let
            expected = OrOfExpandedPattern.make
                [ Predicated
                    { term = mkTop_
                    , predicate = makeCeilPredicate somethingOfA
                    , substitution = mempty
                    }
                , Predicated
                    { term = mkTop_
                    , predicate = makeCeilPredicate somethingOfB
                    , substitution = mempty
                    }
                ]
        actual <- evaluate mockMetadataTools
            (makeCeil
                [somethingOfAExpanded, somethingOfBExpanded]
            )
        assertEqualWithExplanation "" expected actual
    , testCase "Ceil - bool operations"
        (do
            -- ceil(top) = top
            actual1 <- evaluate mockMetadataTools
                (makeCeil
                    [ExpandedPattern.top]
                )
            assertEqualWithExplanation "ceil(top)"
                (OrOfExpandedPattern.make
                    [ ExpandedPattern.top ]
                )
                actual1
            -- ceil(bottom) = bottom
            actual2 <- evaluate mockMetadataTools
                (makeCeil
                    []
                )
            assertEqualWithExplanation "ceil(bottom)"
                (OrOfExpandedPattern.make
                    []
                )
                actual2
        )
    , testCase "expanded Ceil - bool operations"
        (do
            -- ceil(top) = top
            actual1 <- makeEvaluate mockMetadataTools
                (ExpandedPattern.top :: CommonExpandedPattern Object)
            assertEqualWithExplanation "ceil(top)"
                (OrOfExpandedPattern.make
                    [ ExpandedPattern.top ]
                )
                actual1
            -- ceil(bottom) = bottom
            actual2 <- makeEvaluate mockMetadataTools
                (ExpandedPattern.bottom :: CommonExpandedPattern Object)
            assertEqualWithExplanation "ceil(bottom)"
                (OrOfExpandedPattern.make
                    []
                )
                actual2
        )
    , testCase "ceil with predicates and substitutions" $ do
        -- if term is not functional, then
        -- ceil(term and predicate and subst)
        --     = top and (ceil(term) and predicate) and subst
        let
            expected = OrOfExpandedPattern.make
                [ Predicated
                    { term = mkTop_
                    , predicate =
                        makeAndPredicate
                            (makeEqualsPredicate fOfA gOfA)
                            (makeCeilPredicate somethingOfA)
                    , substitution = Substitution.unsafeWrap [(Mock.x, fOfB)]
                    }
                ]
        actual <- makeEvaluate mockMetadataTools
            Predicated
                { term = somethingOfA
                , predicate = makeEqualsPredicate fOfA gOfA
                , substitution = Substitution.wrap [(Mock.x, fOfB)]
                }
        assertEqualWithExplanation "ceil(something(a) and equals(f(a), g(a)))"
            expected
            actual
    , let
        constructorTerm = Mock.constr20 somethingOfA somethingOfB
      in
        testCase "ceil with constructors" $ do
            -- if term is a non-functional-constructor(params), then
            -- ceil(term and predicate and subst)
            --     = top and (ceil(term) and predicate) and subst
            let
                expected = OrOfExpandedPattern.make
                    [ Predicated
                        { term = mkTop_
                        , predicate =
                            makeAndPredicate
                                (makeEqualsPredicate fOfA gOfA)
                                (makeAndPredicate
                                    (makeCeilPredicate somethingOfA)
                                    (makeCeilPredicate somethingOfB)
                                )
                        , substitution =
                            Substitution.unsafeWrap [(Mock.x, fOfB)]
                        }
                    ]
            actual <- makeEvaluate mockMetadataTools
                Predicated
                    { term = constructorTerm
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution = Substitution.wrap [(Mock.x, fOfB)]
                    }
            assertEqualWithExplanation
                "ceil(constr(something(a), something(b)) and eq(f(a), g(a)))"
                expected
                actual
    , testCase "ceil of constructors is top" $ do
        let
            expected = OrOfExpandedPattern.make [ExpandedPattern.top]
        actual <- makeEvaluate mockMetadataTools
            Predicated
                { term = Mock.constr10 Mock.a
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertEqualWithExplanation "" expected actual
    , testCase "ceil with functional symbols" $ do
        -- if term is a functional(params), then
        -- ceil(term and predicate and subst)
        --     = top and (ceil(params) and predicate) and subst
        let
            expected = OrOfExpandedPattern.make
                [ Predicated
                    { term = mkTop_
                    , predicate =
                        makeAndPredicate
                            (makeEqualsPredicate fOfA gOfA)
                            (makeAndPredicate
                                (makeCeilPredicate somethingOfA)
                                (makeCeilPredicate somethingOfB)
                            )
                    , substitution = Substitution.unsafeWrap [(Mock.x, fOfB)]
                    }
                ]
        actual <- makeEvaluate mockMetadataTools
            Predicated
                { term = Mock.functional20 somethingOfA somethingOfB
                , predicate = makeEqualsPredicate fOfA gOfA
                , substitution = Substitution.wrap [(Mock.x, fOfB)]
                }
        assertEqualWithExplanation
            "ceil(functional(something(a), something(b)) and eq(f(a), g(a)))"
            expected
            actual
    , testCase "ceil with function symbols" $ do
        -- if term is a function(params), then
        -- ceil(term and predicate and subst)
        --     = top and (ceil(term) and predicate) and subst
        let
            expected = OrOfExpandedPattern.make
                [ Predicated
                    { term = mkTop_
                    , predicate =
                        makeAndPredicate
                            (makeEqualsPredicate fOfA gOfA)
                            (makeCeilPredicate fOfA)
                    , substitution = Substitution.unsafeWrap [(Mock.x, fOfB)]
                    }
                ]
        actual <- makeEvaluate mockMetadataTools
            Predicated
                { term = fOfA
                , predicate = makeEqualsPredicate fOfA gOfA
                , substitution = Substitution.wrap [(Mock.x, fOfB)]
                }
        assertEqualWithExplanation
            "ceil(f(a)) and eq(f(a), g(a)))"
            expected
            actual
    , testCase "ceil with function symbols" $ do
        -- if term is a functional(params), then
        -- ceil(term and predicate and subst)
        --     = top and (ceil(params) and predicate) and subst
        let
            expected = OrOfExpandedPattern.make
                [ Predicated
                    { term = mkTop_
                    , predicate =
                        makeAndPredicate
                            (makeEqualsPredicate fOfA gOfA)
                            (makeCeilPredicate fOfA)
                    , substitution = Substitution.unsafeWrap [(Mock.x, fOfB)]
                    }
                ]
        actual <- makeEvaluate mockMetadataTools
            Predicated
                { term = fOfA
                , predicate = makeEqualsPredicate fOfA gOfA
                , substitution = Substitution.wrap [(Mock.x, fOfB)]
                }
        assertEqualWithExplanation
            "ceil(f(a)) and eq(f(a), g(a)))"
            expected
            actual
    , testCase "ceil with functional terms" $ do
        -- if term is functional, then
        -- ceil(term and predicate and subst)
        --     = top and predicate and subst
        let
            expected = OrOfExpandedPattern.make
                [ Predicated
                    { term = mkTop_
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution = Substitution.unsafeWrap [(Mock.x, fOfB)]
                    }
                ]
        actual <- makeEvaluate mockMetadataTools
            Predicated
                { term = Mock.a
                , predicate = makeEqualsPredicate fOfA gOfA
                , substitution = Substitution.wrap [(Mock.x, fOfB)]
                }
        assertEqualWithExplanation
            "ceil(functional and eq(f(a), g(a)))"
            expected
            actual
    , testCase "ceil with functional composition" $ do
        -- if term is functional(non-funct, non-funct), then
        -- ceil(term and predicate and subst)
        --     = top and
        --       ceil(non-funct) and ceil(non-funct) and predicate and
        --       subst
        let
            expected = OrOfExpandedPattern.make
                [ Predicated
                    { term = mkTop_
                    , predicate =
                        makeAndPredicate
                            (makeEqualsPredicate fOfA gOfA)
                            (makeAndPredicate
                                (makeCeilPredicate fOfA)
                                (makeCeilPredicate fOfB)
                            )
                    , substitution = Substitution.unsafeWrap [(Mock.x, fOfB)]
                    }
                ]
        actual <- makeEvaluate mockMetadataTools
            Predicated
                { term = Mock.functional20 fOfA fOfB
                , predicate = makeEqualsPredicate fOfA gOfA
                , substitution = Substitution.wrap [(Mock.x, fOfB)]
                }
        assertEqualWithExplanation
            "ceil(functional(non-funct, non-funct) and eq(f(a), g(a)))"
            expected
            actual
    , testCase "ceil with axioms" $ do
        -- if term is functional(non-funct, non-funct), then
        -- ceil(term and predicate and subst)
        --     = top and
        --       ceil(non-funct) and ceil(non-funct) and predicate and
        --       subst
        let
            expected = OrOfExpandedPattern.make
                [ Predicated
                    { term = mkTop_
                    , predicate =
                        makeAndPredicate
                            (makeEqualsPredicate fOfA gOfA)
                            (makeEqualsPredicate Mock.a Mock.cf)
                    , substitution = Substitution.unsafeWrap [(Mock.x, fOfB)]
                    }
                ]
        actual <- makeEvaluateWithAxioms
            mockMetadataTools
            (Map.singleton
                (AxiomIdentifier.Ceil
                    (AxiomIdentifier.Application Mock.fId)
                )
                (appliedMockEvaluator
                    Predicated
                        { term = mkTop_
                        , predicate = makeEqualsPredicate Mock.a Mock.cf
                        , substitution = mempty
                        }
                )
            )
            Predicated
                { term = Mock.functional20 fOfA fOfB
                , predicate = makeEqualsPredicate fOfA gOfA
                , substitution = Substitution.wrap [(Mock.x, fOfB)]
                }
        assertEqualWithExplanation
            "ceil(functional(non-funct, non-funct) and eq(f(a), g(a)))"
            expected
            actual
    , testCase "ceil with normal domain value" $ do
        -- ceil(1) = top
        let
            expected = OrOfExpandedPattern.make
                [ Predicated
                    { term = mkTop_
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                ]
        actual <- makeEvaluate mockMetadataTools
            Predicated
                { term =
                    mkDomainValue
                        testSort
                        (Domain.BuiltinPattern
                            $ eraseAnnotations
                            $ mkStringLiteral "a"
                        )
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertEqualWithExplanation "ceil(1)" expected actual
    , testCase "ceil with map domain value" $ do
        -- maps assume that their keys are relatively functional, so
        -- ceil({a->b, c->d}) = ceil(b) and ceil(d)
        let
            expected = OrOfExpandedPattern.make
                [ Predicated
                    { term = mkTop_
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate fOfB)
                            (makeCeilPredicate gOfB)
                    , substitution = mempty
                    }
                ]
        actual <- makeEvaluate mockMetadataTools
            Predicated
                { term =
                    Mock.builtinMap
                        [(asConcrete fOfA, fOfB), (asConcrete gOfA, gOfB)]
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertEqualWithExplanation "ceil(map)" expected actual
    , testCase "ceil with list domain value" $ do
        -- ceil([a, b]) = ceil(a) and ceil(b)
        let
            expected = OrOfExpandedPattern.make
                [ Predicated
                    { term = mkTop_
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate fOfA)
                            (makeCeilPredicate fOfB)
                    , substitution = mempty
                    }
                ]
        actual <- makeEvaluate mockMetadataTools
            Predicated
                { term = Mock.builtinList [fOfA, fOfB]
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertEqualWithExplanation "ceil(list)" expected actual
    , testCase "ceil with set domain value" $ do
        -- sets assume that their elements are relatively functional,
        -- so ceil({a, b}) = top
        let
            expected = OrOfExpandedPattern.make [ ExpandedPattern.top ]
        actual <- makeEvaluate mockMetadataTools
            Predicated
                { term = Mock.builtinSet [asConcrete fOfA, asConcrete fOfB]
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertEqualWithExplanation "ceil(set)" expected actual
    ]
  where
    fOfA :: StepPattern Object Variable
    fOfA = Mock.f Mock.a
    fOfB :: StepPattern Object Variable
    fOfB = Mock.f Mock.b
    gOfA = Mock.g Mock.a
    gOfB = Mock.g Mock.b
    somethingOfA = Mock.plain10 Mock.a
    somethingOfB = Mock.plain10 Mock.b
    somethingOfAExpanded = Predicated
        { term = somethingOfA
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    somethingOfBExpanded = Predicated
        { term = somethingOfB
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    mockMetadataTools =
        Mock.makeMetadataTools
            Mock.attributesMapping
            Mock.headTypeMapping
            Mock.sortAttributesMapping
            Mock.subsorts
    asConcrete p =
        let Just r = asConcreteStepPattern p in r

appliedMockEvaluator
    :: CommonExpandedPattern level -> BuiltinAndAxiomSimplifier level
appliedMockEvaluator result =
    BuiltinAndAxiomSimplifier
    $ mockEvaluator
    $ AttemptedAxiom.Applied AttemptedAxiomResults
        { results = OrOfExpandedPattern.make
            [Test.Kore.Step.Simplification.Ceil.mapVariables result]
        , remainders = OrOfExpandedPattern.make []
        }

mockEvaluator
    :: AttemptedAxiom level variable
    -> MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -> BuiltinAndAxiomSimplifierMap level
    -> StepPattern level variable
    -> Simplifier
        (AttemptedAxiom level variable, SimplificationProof level)
mockEvaluator evaluation _ _ _ _ _ =
    return (evaluation, SimplificationProof)

mapVariables
    ::  ( FreshVariable variable
        , SortedVariable variable
        , MetaOrObject level
        , Ord (variable level)
        )
    => CommonExpandedPattern level
    -> ExpandedPattern level variable
mapVariables =
    ExpandedPattern.mapVariables $ \v ->
        fromVariable v { variableCounter = Just (Sup.Element 1) }

makeCeil
    :: Ord (variable Object)
    => [ExpandedPattern Object variable]
    -> Ceil Object (OrOfExpandedPattern Object variable)
makeCeil patterns =
    Ceil
        { ceilOperandSort = testSort
        , ceilResultSort  = testSort
        , ceilChild       = OrOfExpandedPattern.make patterns
        }

evaluate
    ::  ( MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> Ceil level (CommonOrOfExpandedPattern level)
    -> IO (CommonOrOfExpandedPattern level)
evaluate tools ceil =
    (<$>) fst
    $ SMT.runSMT SMT.defaultConfig
    $ evalSimplifier emptyLogger noRepl
    $ Ceil.simplify
        tools
        (Mock.substitutionSimplifier tools)
        (Simplifier.create tools Map.empty)
        Map.empty
        ceil

makeEvaluate
    ::  ( MetaOrObject level )
    => MetadataTools level StepperAttributes
    -> CommonExpandedPattern level
    -> IO (CommonOrOfExpandedPattern level)
makeEvaluate tools child =
    makeEvaluateWithAxioms tools Map.empty child

makeEvaluateWithAxioms
    ::  ( MetaOrObject level )
    => MetadataTools level StepperAttributes
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from symbol IDs to defined functions
    -> CommonExpandedPattern level
    -> IO (CommonOrOfExpandedPattern level)
makeEvaluateWithAxioms tools axiomIdToSimplifier child =
    (<$>) fst
    $ SMT.runSMT SMT.defaultConfig
    $ evalSimplifier emptyLogger noRepl
    $ Ceil.makeEvaluate
        tools
        (Mock.substitutionSimplifier tools)
        (Simplifier.create tools axiomIdToSimplifier)
        axiomIdToSimplifier
        child
