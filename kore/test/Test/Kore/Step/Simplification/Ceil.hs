module Test.Kore.Step.Simplification.Ceil
    ( test_ceilSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import qualified Data.Map as Map

import qualified Data.Sup as Sup
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike as TermLike
import           Kore.Logger.Output as Logger
                 ( emptyLogger )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeCeilPredicate, makeEqualsPredicate,
                 makeTruePredicate )
import           Kore.Step.Axiom.Data
                 ( AttemptedAxiom,
                 AttemptedAxiomResults (AttemptedAxiomResults),
                 BuiltinAndAxiomSimplifier (BuiltinAndAxiomSimplifier),
                 BuiltinAndAxiomSimplifierMap )
import qualified Kore.Step.Axiom.Data as AttemptedAxiomResults
                 ( AttemptedAxiomResults (..) )
import qualified Kore.Step.Axiom.Data as AttemptedAxiom
                 ( AttemptedAxiom (..) )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
                 ( AxiomIdentifier (..) )
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluate, simplify )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, Simplifier, TermLikeSimplifier,
                 evalSimplifier )
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Variables.Fresh
                 ( FreshVariable )
import qualified SMT

import           Test.Kore.Comparators ()
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
            expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate = makeCeilPredicate somethingOfA
                    , substitution = mempty
                    }
                , Conditional
                    { term = mkTop_
                    , predicate = makeCeilPredicate somethingOfB
                    , substitution = mempty
                    }
                ]
        actual <- evaluate Mock.metadataTools
            (makeCeil
                [somethingOfAExpanded, somethingOfBExpanded]
            )
        assertEqualWithExplanation "" expected actual
    , testCase "Ceil - bool operations"
        (do
            -- ceil(top) = top
            actual1 <- evaluate Mock.metadataTools
                (makeCeil
                    [Pattern.top]
                )
            assertEqualWithExplanation "ceil(top)"
                (OrPattern.fromPatterns
                    [ Pattern.top ]
                )
                actual1
            -- ceil(bottom) = bottom
            actual2 <- evaluate Mock.metadataTools
                (makeCeil
                    []
                )
            assertEqualWithExplanation "ceil(bottom)"
                (OrPattern.fromPatterns
                    []
                )
                actual2
        )
    , testCase "expanded Ceil - bool operations"
        (do
            -- ceil(top) = top
            actual1 <- makeEvaluate Mock.metadataTools
                (Pattern.top :: Pattern Variable)
            assertEqualWithExplanation "ceil(top)"
                (OrPattern.fromPatterns
                    [ Pattern.top ]
                )
                actual1
            -- ceil(bottom) = bottom
            actual2 <- makeEvaluate Mock.metadataTools
                (Pattern.bottom :: Pattern Variable)
            assertEqualWithExplanation "ceil(bottom)"
                (OrPattern.fromPatterns
                    []
                )
                actual2
        )
    , testCase "ceil with predicates and substitutions" $ do
        -- if term is not functional, then
        -- ceil(term and predicate and subst)
        --     = top and (ceil(term) and predicate) and subst
        let
            expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate =
                        makeAndPredicate
                        (makeCeilPredicate somethingOfA)
                        (makeEqualsPredicate fOfA gOfA)
                    , substitution = Substitution.unsafeWrap [(Mock.x, fOfB)]
                    }
                ]
        actual <- makeEvaluate Mock.metadataTools
            Conditional
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
                expected = OrPattern.fromPatterns
                    [ Conditional
                        { term = mkTop_
                        , predicate =
                            makeAndPredicate
                                (makeAndPredicate
                                    (makeCeilPredicate somethingOfA)
                                    (makeCeilPredicate somethingOfB)
                                )
                                (makeEqualsPredicate fOfA gOfA)
                        , substitution =
                            Substitution.unsafeWrap [(Mock.x, fOfB)]
                        }
                    ]
            actual <- makeEvaluate Mock.metadataTools
                Conditional
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
            expected = OrPattern.fromPatterns [Pattern.top]
        actual <- makeEvaluate Mock.metadataTools
            Conditional
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
            expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate =
                        makeAndPredicate
                            (makeAndPredicate
                                (makeCeilPredicate somethingOfA)
                                (makeCeilPredicate somethingOfB)
                            )
                            (makeEqualsPredicate fOfA gOfA)
                    , substitution = Substitution.unsafeWrap [(Mock.x, fOfB)]
                    }
                ]
        actual <- makeEvaluate Mock.metadataTools
            Conditional
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
            expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate fOfA)
                            (makeEqualsPredicate fOfA gOfA)
                    , substitution = Substitution.unsafeWrap [(Mock.x, fOfB)]
                    }
                ]
        actual <- makeEvaluate Mock.metadataTools
            Conditional
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
            expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate fOfA)
                            (makeEqualsPredicate fOfA gOfA)
                    , substitution = Substitution.unsafeWrap [(Mock.x, fOfB)]
                    }
                ]
        actual <- makeEvaluate Mock.metadataTools
            Conditional
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
            expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution = Substitution.unsafeWrap [(Mock.x, fOfB)]
                    }
                ]
        actual <- makeEvaluate Mock.metadataTools
            Conditional
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
            expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate =
                        makeAndPredicate
                            (makeAndPredicate
                                (makeCeilPredicate fOfA)
                                (makeCeilPredicate fOfB)
                            )
                            (makeEqualsPredicate fOfA gOfA)
                    , substitution = Substitution.unsafeWrap [(Mock.x, fOfB)]
                    }
                ]
        actual <- makeEvaluate Mock.metadataTools
            Conditional
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
            expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate =
                        makeAndPredicate
                            (makeEqualsPredicate Mock.a Mock.cf)
                            (makeEqualsPredicate fOfA gOfA)
                    , substitution = Substitution.unsafeWrap [(Mock.x, fOfB)]
                    }
                ]
        actual <- makeEvaluateWithAxioms
            Mock.metadataTools
            (Map.singleton
                (AxiomIdentifier.Ceil
                    (AxiomIdentifier.Application Mock.fId)
                )
                (appliedMockEvaluator
                    Conditional
                        { term = mkTop_
                        , predicate = makeEqualsPredicate Mock.a Mock.cf
                        , substitution = mempty
                        }
                )
            )
            Conditional
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
            expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                ]
        actual <- makeEvaluate Mock.metadataTools
            Conditional
                { term =
                    mkBuiltin
                        (Domain.BuiltinExternal Domain.External
                            { domainValueSort = Mock.testSort
                            , domainValueChild = mkStringLiteral "a"
                            }
                        )
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertEqualWithExplanation "ceil(1)" expected actual
    , testCase "ceil with map domain value" $ do
        -- maps assume that their keys are relatively functional, so
        -- ceil({a->b, c->d}) = ceil(b) and ceil(d)
        let
            expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate fOfB)
                            (makeCeilPredicate gOfB)
                    , substitution = mempty
                    }
                ]
        actual <- makeEvaluate Mock.metadataTools
            Conditional
                { term =
                    Mock.builtinMap
                        [(asConcrete' fOfA, fOfB), (asConcrete' gOfA, gOfB)]
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertEqualWithExplanation "ceil(map)" expected actual
    , testCase "ceil with list domain value" $ do
        -- ceil([a, b]) = ceil(a) and ceil(b)
        let
            expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate fOfA)
                            (makeCeilPredicate fOfB)
                    , substitution = mempty
                    }
                ]
        actual <- makeEvaluate Mock.metadataTools
            Conditional
                { term = Mock.builtinList [fOfA, fOfB]
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertEqualWithExplanation "ceil(list)" expected actual
    , testCase "ceil with set domain value" $ do
        -- sets assume that their elements are relatively functional,
        -- so ceil({a, b}) = top
        let
            expected = OrPattern.fromPatterns [ Pattern.top ]
        actual <- makeEvaluate Mock.metadataTools
            Conditional
                { term = Mock.builtinSet [asConcrete' fOfA, asConcrete' fOfB]
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertEqualWithExplanation "ceil(set)" expected actual
    ]
  where
    fOfA :: TermLike Variable
    fOfA = Mock.f Mock.a
    fOfB :: TermLike Variable
    fOfB = Mock.f Mock.b
    gOfA = Mock.g Mock.a
    gOfB = Mock.g Mock.b
    somethingOfA = Mock.plain10 Mock.a
    somethingOfB = Mock.plain10 Mock.b
    somethingOfAExpanded = Conditional
        { term = somethingOfA
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    somethingOfBExpanded = Conditional
        { term = somethingOfB
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    asConcrete' p = let Just r = TermLike.asConcrete p in r

appliedMockEvaluator
    :: Pattern Variable -> BuiltinAndAxiomSimplifier
appliedMockEvaluator result =
    BuiltinAndAxiomSimplifier
    $ mockEvaluator
    $ AttemptedAxiom.Applied AttemptedAxiomResults
        { results = OrPattern.fromPatterns
            [Test.Kore.Step.Simplification.Ceil.mapVariables result]
        , remainders = OrPattern.fromPatterns []
        }

mockEvaluator
    :: AttemptedAxiom variable
    -> SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -> TermLike variable
    -> Simplifier (AttemptedAxiom variable)
mockEvaluator evaluation _ _ _ _ _ =
    return evaluation

mapVariables
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Ord variable
        )
    => Pattern Variable
    -> Pattern variable
mapVariables =
    Pattern.mapVariables $ \v ->
        fromVariable v { variableCounter = Just (Sup.Element 1) }

makeCeil
    :: Ord variable
    => [Pattern variable]
    -> Ceil Sort (OrPattern variable)
makeCeil patterns =
    Ceil
        { ceilOperandSort = testSort
        , ceilResultSort  = testSort
        , ceilChild       = OrPattern.fromPatterns patterns
        }

evaluate
    :: SmtMetadataTools StepperAttributes
    -> Ceil Sort (OrPattern Variable)
    -> IO (OrPattern Variable)
evaluate tools ceil =
    SMT.runSMT SMT.defaultConfig
    $ evalSimplifier emptyLogger
    $ Ceil.simplify
        tools
        (Mock.substitutionSimplifier tools)
        (Simplifier.create tools Map.empty)
        Map.empty
        ceil

makeEvaluate
    :: SmtMetadataTools StepperAttributes
    -> Pattern Variable
    -> IO (OrPattern Variable)
makeEvaluate tools child =
    makeEvaluateWithAxioms tools Map.empty child

makeEvaluateWithAxioms
    :: SmtMetadataTools StepperAttributes
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    -> Pattern Variable
    -> IO (OrPattern Variable)
makeEvaluateWithAxioms tools axiomIdToSimplifier child =
    SMT.runSMT SMT.defaultConfig
    $ evalSimplifier emptyLogger
    $ Ceil.makeEvaluate
        tools
        (Mock.substitutionSimplifier tools)
        (Simplifier.create tools axiomIdToSimplifier)
        axiomIdToSimplifier
        child
