module Test.Kore.Step.Simplification.Application
    ( test_applicationSimplification
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.List as List
import qualified Data.Map as Map

import           Data.Sup
import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike as TermLike
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeEqualsPredicate, makeTruePredicate )
import           Kore.Step.Axiom.EvaluationStrategy
                 ( firstFullEvaluation )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
                 ( AxiomIdentifier (..) )
import           Kore.Step.Simplification.Application
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.Data as AttemptedAxiom
                 ( AttemptedAxiom (..) )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
                 ( Unparse )
import           Kore.Variables.Fresh
import           Kore.Variables.UnifiedVariable
                 ( UnifiedVariable (..) )
import qualified SMT

import           Test.Kore
import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSimplifiers as Mock
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Kore.Step.Simplifier
                 ( mockSimplifier )
import           Test.Tasty.HUnit.Extensions

test_applicationSimplification :: [TestTree]
test_applicationSimplification =
    [ testCase "Application - or distribution" $ do
        -- sigma(a or b, c or d) =
        --     sigma(b, d) or sigma(b, c) or sigma(a, d) or sigma(a, c)
        let expect =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = Mock.sigma Mock.a Mock.c
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    , Conditional
                        { term = Mock.sigma Mock.a Mock.d
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    , Conditional
                        { term = Mock.sigma Mock.b Mock.c
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ,  Conditional
                        { term = Mock.sigma Mock.b Mock.d
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
        actual <-
            evaluate
                (mockSimplifier noSimplification)
                Map.empty
                (makeApplication
                    Mock.sigmaSymbol
                    [ [aExpanded, bExpanded]
                    , [cExpanded, dExpanded]
                    ]
                )
        assertEqualWithExplanation "" expect actual

    , testCase "Application - bottom child makes everything bottom" $ do
        -- sigma(a or b, bottom) = bottom
        let expect = OrPattern.fromPatterns [ Pattern.bottom ]
        actual <-
            evaluate
                (mockSimplifier noSimplification)
                Map.empty
                (makeApplication
                    Mock.sigmaSymbol
                    [ [aExpanded, bExpanded]
                    , []
                    ]
                )
        assertEqualWithExplanation "" expect actual

    , testCase "Applies functions" $ do
        -- f(a) evaluated to g(a).
        let expect = OrPattern.fromPatterns [ gOfAExpanded ]
        actual <-
            evaluate
                (mockSimplifier noSimplification)
                (Map.singleton
                    (AxiomIdentifier.Application Mock.fId)
                    (simplificationEvaluator
                        [ BuiltinAndAxiomSimplifier $ \_ _ _ _ ->
                            return $ AttemptedAxiom.Applied
                                AttemptedAxiomResults
                                    { results =
                                        OrPattern.fromPattern gOfAExpanded
                                    , remainders = OrPattern.bottom
                                    }
                        ]
                    )
                )
                (makeApplication Mock.fSymbol [[aExpanded]])
        assertEqualWithExplanation "" expect actual

    , testGroup "Combines child predicates and substitutions"
        [ testCase "When not applying functions" $ do
            -- sigma(a and f(a)=f(b) and [x=f(a)], b and g(a)=g(b) and [y=g(a)])
            --    = sigma(a, b)
            --        and (f(a)=f(b) and g(a)=g(b))
            --        and [x=f(a), y=g(a)]
            let expect =
                    OrPattern.fromPatterns
                        [ Conditional
                            { term = Mock.sigma Mock.a Mock.b
                            , predicate =
                                makeAndPredicate
                                    (makeEqualsPredicate fOfA fOfB)
                                    (makeEqualsPredicate gOfA gOfB)
                            , substitution = Substitution.unsafeWrap
                                [ (ElemVar Mock.x, fOfA)
                                , (ElemVar Mock.y, gOfA)
                                ]
                            }
                        ]
            actual <-
                evaluate
                    (mockSimplifier noSimplification)
                    Map.empty
                    (makeApplication
                        Mock.sigmaSymbol
                        [   [ Conditional
                                { term = Mock.a
                                , predicate = makeEqualsPredicate fOfA fOfB
                                , substitution =
                                    Substitution.wrap [ (ElemVar Mock.x, fOfA) ]
                                }
                            ]
                        ,   [ Conditional
                                { term = Mock.b
                                , predicate = makeEqualsPredicate gOfA gOfB
                                , substitution =
                                    Substitution.wrap [ (ElemVar Mock.y, gOfA) ]
                                }
                            ]
                        ]
                    )
            assertEqualWithExplanation "" expect actual

        , testCase "When applying functions" $ do
            -- sigma(a and f(a)=f(b) and [x=f(a)], b and g(a)=g(b) and [y=g(a)])
            --    =
            --        f(a) and
            --        (f(a)=f(b) and g(a)=g(b) and f(a)=g(a)) and
            --        [x=f(a), y=g(a), z=f(b)]
            -- if sigma(a, b) => f(a) and f(a)=g(a) and [z=f(b)]
            let ElementVariable z = Mock.z
                z' = ElementVariable z { variableCounter = Just (Element 1) }
                expect =
                    OrPattern.fromPatterns
                        [ Conditional
                            { term = fOfA
                            , predicate =
                                makeAndPredicate
                                    (makeAndPredicate
                                        (makeEqualsPredicate fOfA gOfA)
                                        (makeEqualsPredicate fOfA fOfB)
                                    )
                                    (makeEqualsPredicate gOfA gOfB)
                            , substitution =
                                Substitution.unsafeWrap $ List.sortOn fst
                                    [ (ElemVar z', gOfB)
                                    , (ElemVar Mock.x, fOfA)
                                    , (ElemVar Mock.y, gOfA)
                                    ]
                            }
                        ]
            actual <-
                let
                    zvar
                        :: forall variable
                        .   ( FreshVariable variable
                            , Ord variable
                            , SortedVariable variable
                            )
                        => ElementVariable variable
                    zvar = fromVariable <$> z'
                    result
                        :: forall variable
                        .   ( FreshVariable variable
                            , Ord variable
                            , Show variable
                            , SortedVariable variable
                            , Unparse variable
                            )
                        => AttemptedAxiom variable
                    result = AttemptedAxiom.Applied AttemptedAxiomResults
                        { results = OrPattern.fromPatterns
                            [ Conditional
                                { term = fOfA
                                , predicate = makeEqualsPredicate fOfA gOfA
                                , substitution =
                                    Substitution.wrap [ (ElemVar zvar, gOfB) ]
                                }
                            ]
                        , remainders = OrPattern.fromPatterns []
                        }
                in
                    evaluate
                        (simplifierTermLike Mock.env)
                        (Map.singleton
                            (AxiomIdentifier.Application Mock.sigmaId)
                            (simplificationEvaluator
                                [ BuiltinAndAxiomSimplifier $ \_ _ _ _ ->
                                    return result
                                ]
                            )
                        )
                    (makeApplication
                        Mock.sigmaSymbol
                        [   [ Conditional
                                { term = Mock.a
                                , predicate = makeEqualsPredicate fOfA fOfB
                                , substitution =
                                    Substitution.wrap [ (ElemVar Mock.x, fOfA) ]
                                }
                            ]
                        ,   [ Conditional
                                { term = Mock.b
                                , predicate = makeEqualsPredicate gOfA gOfB
                                , substitution =
                                    Substitution.wrap [ (ElemVar Mock.y, gOfA) ]
                                }
                            ]
                        ]
                    )
            assertEqualWithExplanation "" expect actual
        ]
    ]
  where
    fOfA, fOfB, gOfA, gOfB
        :: (Ord variable, SortedVariable variable, Unparse variable)
        => TermLike variable
    fOfA = Mock.f Mock.a
    fOfB = Mock.f Mock.b
    gOfA = Mock.g Mock.a
    gOfB = Mock.g Mock.b

    aExpanded = Conditional
        { term = Mock.a
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    bExpanded = Conditional
        { term = Mock.b
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    cExpanded = Conditional
        { term = Mock.c
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    dExpanded = Conditional
        { term = Mock.d
        , predicate = makeTruePredicate
        , substitution = mempty
        }

    gOfAExpanded
        :: (Ord variable, SortedVariable variable, Unparse variable)
        => Pattern variable
    gOfAExpanded = Conditional
        { term = gOfA
        , predicate = makeTruePredicate
        , substitution = mempty
        }

    noSimplification :: [(TermLike Variable, [Pattern Variable])]
    noSimplification = []

simplificationEvaluator
    :: [BuiltinAndAxiomSimplifier]
    -> BuiltinAndAxiomSimplifier
simplificationEvaluator = firstFullEvaluation

makeApplication
    :: (Ord variable, Show variable, HasCallStack)
    => Symbol
    -> [[Pattern variable]]
    -> Application Symbol (OrPattern variable)
makeApplication symbol patterns =
    Application
        { applicationSymbolOrAlias = symbol
        , applicationChildren = map OrPattern.fromPatterns patterns
        }

evaluate
    :: TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> Application Symbol (OrPattern Variable)
    -> IO (OrPattern Variable)
evaluate simplifier axiomIdToEvaluator application =
    SMT.runSMT SMT.defaultConfig emptyLogger
    $ evalSimplifier mockEnv
    $ simplify application
  where
    mockEnv =
        Mock.env
            { simplifierPredicate = Mock.substitutionSimplifier
            , simplifierAxioms = axiomIdToEvaluator
            , simplifierTermLike = simplifier
            }
