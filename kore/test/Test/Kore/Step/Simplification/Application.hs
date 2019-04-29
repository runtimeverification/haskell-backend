module Test.Kore.Step.Simplification.Application
    ( test_applicationSimplification
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.List as List
import qualified Data.Map as Map
import           Data.Ord
                 ( comparing )
import qualified Data.Set as Set

import           Data.Sup
import qualified Kore.Annotation.Valid as Valid
import           Kore.AST.Common
                 ( SortedVariable (..) )
import           Kore.AST.Valid
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeEqualsPredicate, makeTruePredicate )
import           Kore.Step.Axiom.Data
import qualified Kore.Step.Axiom.Data as AttemptedAxiom
                 ( AttemptedAxiom (..) )
import           Kore.Step.Axiom.EvaluationStrategy
                 ( firstFullEvaluation )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
                 ( AxiomIdentifier (..) )
import           Kore.Step.OrPattern
                 ( OrPattern )
import qualified Kore.Step.OrPattern as OrPattern
import           Kore.Step.Pattern as Pattern
import           Kore.Step.Simplification.Application
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..), TermLikeSimplifier,
                 evalSimplifier )
import           Kore.Step.TermLike as TermLike
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
                 ( Unparse )
import           Kore.Variables.Fresh
import qualified SMT

import           Test.Kore
import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools )
import qualified Test.Kore.Step.MockSimplifiers as Mock
import           Test.Kore.Step.MockSymbols
                 ( testSort )
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
                mockMetadataTools
                (mockSimplifier noSimplification)
                Map.empty
                (makeApplication
                    testSort
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
                mockMetadataTools
                (mockSimplifier noSimplification)
                Map.empty
                (makeApplication
                    testSort
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
                mockMetadataTools
                (mockSimplifier noSimplification)
                (Map.singleton
                    (AxiomIdentifier.Application Mock.fId)
                    (simplificationEvaluator
                        [ BuiltinAndAxiomSimplifier
                            (const $ const $ const $ const $ const $ return
                                ( AttemptedAxiom.Applied AttemptedAxiomResults
                                    { results =
                                        OrPattern.fromPatterns [gOfAExpanded]
                                    , remainders = OrPattern.fromPatterns []
                                    }
                                , SimplificationProof
                                )
                            )
                        ]
                    )
                )
                (makeApplication
                    testSort
                    Mock.fSymbol
                    [[aExpanded]]
                )
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
                                [ (Mock.x, fOfA)
                                , (Mock.y, gOfA)
                                ]
                            }
                        ]
            actual <-
                evaluate
                    mockMetadataTools
                    (mockSimplifier noSimplification)
                    Map.empty
                    (makeApplication
                        testSort
                        Mock.sigmaSymbol
                        [   [ Conditional
                                { term = Mock.a
                                , predicate = makeEqualsPredicate fOfA fOfB
                                , substitution =
                                    Substitution.wrap [ (Mock.x, fOfA) ]
                                }
                            ]
                        ,   [ Conditional
                                { term = Mock.b
                                , predicate = makeEqualsPredicate gOfA gOfB
                                , substitution =
                                    Substitution.wrap [ (Mock.y, gOfA) ]
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
            let z' = Mock.z { variableCounter = Just (Element 1) }
                expect =
                    OrPattern.fromPatterns
                        [ Conditional
                            { term = fOfA
                            , predicate =
                                makeAndPredicate
                                    (makeEqualsPredicate fOfA gOfA)
                                    (makeAndPredicate
                                        (makeEqualsPredicate fOfA fOfB)
                                        (makeEqualsPredicate gOfA gOfB)
                                    )
                            , substitution =
                                Substitution.unsafeWrap
                                $ List.sortBy (comparing fst)
                                    [ (z', gOfB)
                                    , (Mock.x, fOfA)
                                    , (Mock.y, gOfA)
                                    ]
                            }
                        ]
            actual <-
                let
                    zvar
                        :: forall variable
                        .   ( FreshVariable variable
                            , Ord (variable Object)
                            , SortedVariable variable
                            )
                        => variable Object
                    zvar = fromVariable z'
                    result
                        :: forall variable
                        .   ( FreshVariable variable
                            , Ord (variable Object)
                            , Show (variable Object)
                            , SortedVariable variable
                            , Unparse (variable Object)
                            )
                        => AttemptedAxiom Object variable
                    result = AttemptedAxiom.Applied AttemptedAxiomResults
                        { results = OrPattern.fromPatterns
                            [ Conditional
                                { term = fOfA
                                , predicate = makeEqualsPredicate fOfA gOfA
                                , substitution =
                                    Substitution.wrap [ (zvar, gOfB) ]
                                }
                            ]
                        , remainders = OrPattern.fromPatterns []
                        }
                in
                    evaluate
                        mockMetadataTools
                        (mockSimplifier noSimplification)
                        (Map.singleton
                            (AxiomIdentifier.Application Mock.sigmaId)
                            (simplificationEvaluator
                                [ BuiltinAndAxiomSimplifier
                                    (const $ const $ const $ const $ const $
                                        return (result, SimplificationProof)
                                    )
                                ]
                            )
                        )
                    (makeApplication
                        testSort
                        Mock.sigmaSymbol
                        [   [ Conditional
                                { term = Mock.a
                                , predicate = makeEqualsPredicate fOfA fOfB
                                , substitution =
                                    Substitution.wrap [ (Mock.x, fOfA) ]
                                }
                            ]
                        ,   [ Conditional
                                { term = Mock.b
                                , predicate = makeEqualsPredicate gOfA gOfB
                                , substitution =
                                    Substitution.wrap [ (Mock.y, gOfA) ]
                                }
                            ]
                        ]
                    )
            assertEqualWithExplanation "" expect actual
        ]
    ]
  where
    fOfA, fOfB :: Ord (variable Object) => TermLike variable
    fOfA = Mock.f Mock.a
    fOfB = Mock.f Mock.b

    gOfA, gOfB :: Ord (variable Object) => TermLike variable
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

    gOfAExpanded :: Ord (variable Object) => Pattern Object variable
    gOfAExpanded = Conditional
        { term = gOfA
        , predicate = makeTruePredicate
        , substitution = mempty
        }

    mockMetadataTools =
        Mock.makeMetadataTools
            Mock.attributesMapping
            Mock.headTypeMapping
            Mock.sortAttributesMapping
            Mock.subsorts
            Mock.headSortsMapping
            Mock.smtDeclarations

    noSimplification
        ::  [   ( TermLike Variable
                , ([Pattern level Variable], SimplificationProof level)
                )
            ]
    noSimplification = []

simplificationEvaluator
    :: [BuiltinAndAxiomSimplifier Object]
    -> BuiltinAndAxiomSimplifier Object
simplificationEvaluator = firstFullEvaluation

makeApplication
    :: (Ord (variable Object), Show (variable Object), HasCallStack)
    => Sort Object
    -> SymbolOrAlias Object
    -> [[Pattern Object variable]]
    -> CofreeF
        (Application Object)
        (Valid (variable Object) Object)
        (OrPattern Object variable)
makeApplication patternSort symbol patterns =
    (:<)
        valid
        Application
            { applicationSymbolOrAlias = symbol
            , applicationChildren = map OrPattern.fromPatterns patterns
            }
  where
    termFreeVariables = TermLike.freeVariables . Pattern.term
    valid =
        Valid
            { patternSort
            , freeVariables =
                Set.unions (Set.unions . map termFreeVariables <$> patterns)
            }

evaluate
    ::  ( MetaOrObject level)
    => SmtMetadataTools StepperAttributes
    -> TermLikeSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> CofreeF
        (Application level)
        (Valid (Variable level) level)
        (OrPattern level Variable)
    -> IO (OrPattern level Variable)
evaluate
    tools
    simplifier
    axiomIdToEvaluator
    application
  =
    (<$>) fst
    $ SMT.runSMT SMT.defaultConfig
    $ evalSimplifier emptyLogger
    $ simplify
        tools
        (Mock.substitutionSimplifier tools)
        simplifier
        axiomIdToEvaluator
        application
