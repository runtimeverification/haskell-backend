module Test.Kore.Simplify.Ceil (
    test_ceilSimplification,
) where

import qualified Data.Map.Strict as Map
import qualified Data.Sup as Sup
import Kore.Internal.Condition as Condition
import Kore.Internal.Predicate (
    makeAndPredicate,
    makeCeilPredicate,
    makeEqualsPredicate,
    makeTruePredicate,
 )
import Kore.Internal.SideCondition (
    SideCondition,
 )
import qualified Kore.Internal.SideCondition as SideCondition (
    toRepresentation,
    top,
 )
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition (
    Representation,
 )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike as TermLike
import qualified Kore.Rewrite.Axiom.Identifier as AxiomIdentifier (
    AxiomIdentifier (..),
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import qualified Kore.Simplify.Ceil as Ceil (
    makeEvaluate,
    simplify,
 )
import Kore.Simplify.Simplify
import qualified Kore.Simplify.Simplify as AttemptedAxiom (
    AttemptedAxiom (..),
 )
import Prelude.Kore
import Test.Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Test.Kore.Internal.OrPattern as OrPattern
import Test.Kore.Internal.Pattern as Pattern
import Test.Kore.Rewrite.MockSymbols (
    testSort,
 )
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Kore.Simplify
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_ceilSimplification :: [TestTree]
test_ceilSimplification =
    [ testCase "Ceil - or distribution" $ do
        -- ceil(a or b) = (top and ceil(a)) or (top and ceil(b))
        let expected =
                OrPattern.fromPatterns
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
        actual <-
            evaluate
                ( makeCeil
                    [somethingOfAExpanded, somethingOfBExpanded]
                )
        assertEqual "" expected actual
    , testCase
        "Ceil - bool operations"
        ( do
            -- ceil(top) = top
            actual1 <-
                evaluate
                    ( makeCeil
                        [Pattern.top]
                    )
            assertEqual
                "ceil(top)"
                ( OrPattern.fromPatterns
                    [Pattern.top]
                )
                actual1
            -- ceil(bottom) = bottom
            actual2 <-
                evaluate
                    ( makeCeil
                        []
                    )
            assertEqual
                "ceil(bottom)"
                ( OrPattern.fromPatterns
                    []
                )
                actual2
        )
    , testCase
        "Ceil - sorted bool operations"
        ( do
            -- ceil(top{testSort}) = top
            actual1 <-
                evaluate
                    ( makeCeil
                        [Pattern.fromCondition Mock.testSort Condition.top]
                    )
            assertEqual
                "ceil(top)"
                ( OrPattern.fromPatterns
                    [Pattern.top]
                )
                actual1
        )
    , testCase
        "expanded Ceil - bool operations"
        ( do
            -- ceil(top) = top
            actual1 <- makeEvaluate Pattern.top
            assertEqual
                "ceil(top)"
                ( OrPattern.fromPatterns
                    [Pattern.top]
                )
                actual1
            -- ceil(bottom) = bottom
            actual2 <- makeEvaluate Pattern.bottom
            assertEqual
                "ceil(bottom)"
                ( OrPattern.fromPatterns
                    []
                )
                actual2
        )
    , testCase "ceil with predicates and substitutions" $ do
        -- if term is not functional, then
        -- ceil(term and predicate and subst)
        --     = top and (ceil(term) and predicate) and subst
        let expected =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = mkTop_
                        , predicate =
                            makeAndPredicate
                                (makeCeilPredicate somethingOfA)
                                (makeEqualsPredicate fOfA gOfA)
                        , substitution =
                            Substitution.unsafeWrap [(inject Mock.xConfig, fOfB)]
                        }
                    ]
        actual <-
            makeEvaluate
                Conditional
                    { term = somethingOfA
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [(inject Mock.xConfig, fOfB)]
                    }
        assertEqual
            "ceil(something(a) and equals(f(a), g(a)))"
            expected
            actual
    , let constructorTerm = Mock.constr20 somethingOfA somethingOfB
       in testCase "ceil with constructors" $ do
            -- if term is a non-functional-constructor(params), then
            -- ceil(term and predicate and subst)
            --     = top and (ceil(term) and predicate) and subst
            let expected =
                    OrPattern.fromPatterns
                        [ Conditional
                            { term = mkTop_
                            , predicate =
                                makeAndPredicate
                                    ( makeAndPredicate
                                        (makeCeilPredicate somethingOfA)
                                        (makeCeilPredicate somethingOfB)
                                    )
                                    (makeEqualsPredicate fOfA gOfA)
                            , substitution =
                                Substitution.unsafeWrap
                                    [(inject Mock.xConfig, fOfB)]
                            }
                        ]
            actual <-
                makeEvaluate
                    Conditional
                        { term = constructorTerm
                        , predicate = makeEqualsPredicate fOfA gOfA
                        , substitution =
                            Substitution.wrap $
                                Substitution.mkUnwrappedSubstitution
                                    [(inject Mock.xConfig, fOfB)]
                        }
            assertEqual
                "ceil(constr(something(a), something(b)) and eq(f(a), g(a)))"
                expected
                actual
    , testCase "ceil of constructors is top" $ do
        let expected = OrPattern.fromPatterns [Pattern.top]
        actual <-
            makeEvaluate
                Conditional
                    { term = Mock.constr10 Mock.a
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        assertEqual "" expected actual
    , testCase "ceil with functional symbols" $ do
        -- if term is a functional(params), then
        -- ceil(term and predicate and subst)
        --     = top and (ceil(params) and predicate) and subst
        let expected =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = mkTop_
                        , predicate =
                            makeAndPredicate
                                ( makeAndPredicate
                                    (makeCeilPredicate somethingOfA)
                                    (makeCeilPredicate somethingOfB)
                                )
                                (makeEqualsPredicate fOfA gOfA)
                        , substitution =
                            Substitution.unsafeWrap [(inject Mock.xConfig, fOfB)]
                        }
                    ]
        actual <-
            makeEvaluate
                Conditional
                    { term = Mock.functional20 somethingOfA somethingOfB
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [(inject Mock.xConfig, fOfB)]
                    }
        assertEqual
            "ceil(functional(something(a), something(b)) and eq(f(a), g(a)))"
            expected
            actual
    , testCase "ceil with function symbols" $ do
        -- if term is a function(params), then
        -- ceil(term and predicate and subst)
        --     = top and (ceil(term) and predicate) and subst
        let expected =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = mkTop_
                        , predicate =
                            makeAndPredicate
                                (makeCeilPredicate fOfA)
                                (makeEqualsPredicate fOfA gOfA)
                        , substitution =
                            Substitution.unsafeWrap [(inject Mock.xConfig, fOfB)]
                        }
                    ]
        actual <-
            makeEvaluate
                Conditional
                    { term = fOfA
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [(inject Mock.xConfig, fOfB)]
                    }
        assertEqual
            "ceil(f(a)) and eq(f(a), g(a)))"
            expected
            actual
    , testCase "ceil with functional terms" $ do
        -- if term is functional, then
        -- ceil(term and predicate and subst)
        --     = top and predicate and subst
        let expected =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = mkTop_
                        , predicate = makeEqualsPredicate fOfA gOfA
                        , substitution =
                            Substitution.unsafeWrap [(inject Mock.xConfig, fOfB)]
                        }
                    ]
        actual <-
            makeEvaluate
                Conditional
                    { term = Mock.a
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [(inject Mock.xConfig, fOfB)]
                    }
        assertEqual
            "ceil(functional and eq(f(a), g(a)))"
            expected
            actual
    , testCase "ceil with functional composition" $ do
        -- if term is functional(non-funct, non-funct), then
        -- ceil(term and predicate and subst)
        --     = top and
        --       ceil(non-funct) and ceil(non-funct) and predicate and
        --       subst
        let expected =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = mkTop_
                        , predicate =
                            makeAndPredicate
                                ( makeAndPredicate
                                    (makeCeilPredicate fOfA)
                                    (makeCeilPredicate fOfB)
                                )
                                (makeEqualsPredicate fOfA gOfA)
                        , substitution =
                            Substitution.unsafeWrap [(inject Mock.xConfig, fOfB)]
                        }
                    ]
        actual <-
            makeEvaluate
                Conditional
                    { term = Mock.functional20 fOfA fOfB
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [(inject Mock.xConfig, fOfB)]
                    }
        assertEqual
            "ceil(functional(non-funct, non-funct) and eq(f(a), g(a)))"
            expected
            actual
    , testCase "ceil with axioms" $ do
        -- if term is functional(non-funct, non-funct), then
        -- ceil(term and predicate and subst)
        --     = top and
        --       ceil(non-funct) and ceil(non-funct) and predicate and
        --       subst
        let expected =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = mkTop_
                        , predicate =
                            makeAndPredicate
                                (makeEqualsPredicate Mock.a Mock.cf)
                                (makeEqualsPredicate fOfA gOfA)
                        , substitution =
                            Substitution.unsafeWrap [(inject Mock.xConfig, fOfB)]
                        }
                    ]
        actual <-
            makeEvaluateWithAxioms
                ( Map.singleton
                    ( AxiomIdentifier.Ceil
                        (AxiomIdentifier.Application Mock.fId)
                    )
                    ( appliedMockEvaluator
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
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [(inject Mock.xConfig, fOfB)]
                    }
        assertEqual
            "ceil(functional(non-funct, non-funct) and eq(f(a), g(a)))"
            expected
            actual
    , testCase "ceil with normal domain value" $ do
        -- ceil(1) = top
        let expected =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = mkTop_
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
        actual <-
            makeEvaluate $
                Pattern.fromTermLike $
                    mkDomainValue
                        DomainValue
                            { domainValueSort = Mock.testSort
                            , domainValueChild = mkStringLiteral "a"
                            }
        assertEqual "ceil(1)" expected actual
    , testCase "ceil with list domain value" $ do
        -- ceil([a, b]) = ceil(a) and ceil(b)
        let expected =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = mkTop_
                        , predicate =
                            makeAndPredicate
                                (makeCeilPredicate fOfA)
                                (makeCeilPredicate fOfB)
                        , substitution = mempty
                        }
                    ]
        actual <-
            makeEvaluate
                Conditional
                    { term = Mock.builtinList [fOfA, fOfB]
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        assertEqual "ceil(list)" expected actual
    , testCase "ceil of sort injection" $ do
        let expected =
                OrPattern.fromPattern
                    Conditional
                        { term = mkTop_
                        , predicate = makeCeilPredicate fOfA
                        , substitution = mempty
                        }
        actual <-
            (makeEvaluate . Pattern.fromTermLike)
                (Mock.sortInjection Mock.topSort (TermLike.markSimplified fOfA))
        assertEqual "ceil(f(a))" expected actual
        assertBool
            "simplified"
            (OrPattern.isSimplified sideRepresentation actual)
    ]
  where
    fOfA :: TermLike RewritingVariableName
    fOfA = Mock.f Mock.a
    fOfB :: TermLike RewritingVariableName
    fOfB = Mock.f Mock.b
    gOfA = Mock.g Mock.a
    somethingOfA = Mock.plain10 Mock.a
    somethingOfB = Mock.plain10 Mock.b
    somethingOfAExpanded =
        Conditional
            { term = somethingOfA
            , predicate = makeTruePredicate
            , substitution = mempty
            }
    somethingOfBExpanded =
        Conditional
            { term = somethingOfB
            , predicate = makeTruePredicate
            , substitution = mempty
            }

appliedMockEvaluator ::
    Pattern RewritingVariableName -> BuiltinAndAxiomSimplifier
appliedMockEvaluator result =
    BuiltinAndAxiomSimplifier $
        mockEvaluator $
            AttemptedAxiom.Applied
                AttemptedAxiomResults
                    { results =
                        OrPattern.fromPatterns
                            [Test.Kore.Simplify.Ceil.mapVariables result]
                    , remainders = OrPattern.fromPatterns []
                    }

mockEvaluator ::
    MonadSimplify simplifier =>
    AttemptedAxiom RewritingVariableName ->
    TermLike RewritingVariableName ->
    SideCondition RewritingVariableName ->
    simplifier (AttemptedAxiom RewritingVariableName)
mockEvaluator evaluation _ _ = return evaluation

mapVariables ::
    forall variable.
    InternalVariable variable =>
    Pattern RewritingVariableName ->
    Pattern variable
mapVariables =
    Pattern.mapVariables (pure worker)
  where
    worker :: RewritingVariableName -> variable
    worker v =
        fromVariableName $
            (from @RewritingVariableName @VariableName v)
                { counter = Just (Sup.Element 1)
                }

makeCeil ::
    [Pattern RewritingVariableName] ->
    Ceil Sort (OrPattern RewritingVariableName)
makeCeil patterns =
    Ceil
        { ceilOperandSort = testSort
        , ceilResultSort = testSort
        , ceilChild = OrPattern.fromPatterns patterns
        }

evaluate ::
    Ceil Sort (OrPattern RewritingVariableName) ->
    IO (OrPattern RewritingVariableName)
evaluate ceil =
    runSimplifier mockEnv $
        Ceil.simplify SideCondition.top ceil
  where
    mockEnv = Mock.env

makeEvaluate ::
    Pattern RewritingVariableName -> IO (OrPattern RewritingVariableName)
makeEvaluate = makeEvaluateWithAxioms Map.empty

makeEvaluateWithAxioms ::
    -- | Map from symbol IDs to defined functions
    BuiltinAndAxiomSimplifierMap ->
    Pattern RewritingVariableName ->
    IO (OrPattern RewritingVariableName)
makeEvaluateWithAxioms axiomIdToSimplifier child =
    runSimplifier mockEnv $
        Ceil.makeEvaluate SideCondition.top child
  where
    mockEnv = Mock.env{simplifierAxioms = axiomIdToSimplifier}

sideRepresentation :: SideCondition.Representation
sideRepresentation =
    SideCondition.toRepresentation
        (SideCondition.top :: SideCondition RewritingVariableName)
