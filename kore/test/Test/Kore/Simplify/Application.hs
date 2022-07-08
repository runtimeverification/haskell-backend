module Test.Kore.Simplify.Application (
    test_applicationSimplification,
) where

import Control.Lens qualified as Lens
import Data.Generics.Product (
    field,
 )
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Sup
import Kore.Internal.MultiAnd qualified as MultiAnd
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    makeAndPredicate,
    makeEqualsPredicate,
    makeTruePredicate,
 )
import Kore.Internal.Predicate qualified as Predicate
import Kore.Internal.SideCondition qualified as SideCondition (
    top,
 )
import Kore.Internal.Substitution qualified as Substitution
import Kore.Internal.TermLike as TermLike
import Kore.Rewrite.Axiom.Identifier qualified as AxiomIdentifier (
    AxiomIdentifier (..),
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    mkConfigVariable,
 )
import Kore.Simplify.Application
import Kore.Simplify.Simplify
import Kore.Simplify.Simplify qualified as AttemptedAxiom (
    AttemptedAxiom (..),
 )
import Kore.Syntax.Variable qualified as Variable
import Prelude.Kore
import Test.Kore.Internal.Pattern qualified as Pattern
import Test.Kore.Rewrite.MockSymbols qualified as Mock
import Test.Kore.Simplify
import Test.Tasty
import Test.Tasty.HUnit.Ext

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
                    , Conditional
                        { term = Mock.sigma Mock.b Mock.d
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
        actual <-
            evaluate
                Map.empty
                ( makeApplication
                    Mock.sigmaSymbol
                    [ [aExpanded, bExpanded]
                    , [cExpanded, dExpanded]
                    ]
                )
        assertEqual "" expect actual
    , testCase "Application - bottom child makes everything bottom" $ do
        -- sigma(a or b, bottom) = bottom
        let expect = OrPattern.fromPatterns [Pattern.bottomOf Mock.testSort]
        actual <-
            evaluate
                Map.empty
                ( makeApplication
                    Mock.sigmaSymbol
                    [ [aExpanded, bExpanded]
                    , []
                    ]
                )
        assertEqual "" expect actual
    , testCase "Application - preserves sort for top child" $ do
        -- sigma(a, top) = top
        let expect =
                OrPattern.fromPatterns
                    [ Pattern.fromTermLike (Mock.sigma Mock.a (mkTop Mock.testSort))
                    ]
        actual <-
            evaluate
                Map.empty
                ( makeApplication
                    Mock.sigmaSymbol
                    [ [aExpanded]
                    , [Pattern.topOf Mock.testSort]
                    ]
                )
        assertEqual "" expect actual
    , testCase "Applies functions" $ do
        -- f(a) evaluated to g(a).
        let expect = OrPattern.fromPatterns [gOfAExpanded]
        actual <-
            evaluate
                ( Map.singleton
                    (AxiomIdentifier.Application Mock.fId)
                    ( simplificationEvaluator
                        [ BuiltinAndAxiomSimplifier $ \_ _ ->
                            return $
                                AttemptedAxiom.Applied
                                    AttemptedAxiomResults
                                        { results =
                                            OrPattern.fromPattern gOfAExpanded
                                        , remainders = OrPattern.bottom
                                        }
                        ]
                    )
                )
                (makeApplication Mock.fSymbol [[aExpanded]])
        assertEqual "" expect actual
    , testGroup
        "Combines child predicates and substitutions"
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
                                    ( makeEqualsPredicate
                                        fOfA
                                        fOfB
                                    )
                                    (makeEqualsPredicate gOfA gOfB)
                            , substitution =
                                Substitution.unsafeWrap
                                    [ (inject Mock.xConfig, fOfA)
                                    , (inject Mock.yConfig, gOfA)
                                    ]
                            }
                        ]
            actual <-
                evaluate
                    Map.empty
                    ( makeApplication
                        Mock.sigmaSymbol
                        [
                            [ Conditional
                                { term = Mock.a
                                , predicate = makeEqualsPredicate fOfA fOfB
                                , substitution =
                                    Substitution.wrap $
                                        Substitution.mkUnwrappedSubstitution
                                            [(inject Mock.xConfig, fOfA)]
                                }
                            ]
                        ,
                            [ Conditional
                                { term = Mock.b
                                , predicate = makeEqualsPredicate gOfA gOfB
                                , substitution =
                                    Substitution.wrap $
                                        Substitution.mkUnwrappedSubstitution
                                            [(inject Mock.yConfig, gOfA)]
                                }
                            ]
                        ]
                    )
            assertEqual "" expect actual
        , testCase "When applying functions" $ do
            -- sigma(a and f(a)=f(b) and [x=f(a)], b and g(a)=g(b) and [y=g(a)])
            --    =
            --        f(a) and
            --        (f(a)=f(b) and g(a)=g(b) and f(a)=g(a)) and
            --        [x=f(a), y=g(a), z=f(b)]
            -- if sigma(a, b) => f(a) and f(a)=g(a) and [z=f(b)]
            let z' =
                    Lens.set
                        ( field @"variableName"
                            . Lens.mapped
                            . field @"counter"
                        )
                        (Just (Element 1))
                        Mock.z
                        & Variable.mapElementVariable (pure mkConfigVariable)
                expects =
                    OrPattern.fromPatterns
                        [ Conditional
                            { term = fOfA
                            , predicate =
                                (Predicate.fromMultiAnd . MultiAnd.make)
                                    [ makeEqualsPredicate fOfA fOfB
                                    , makeEqualsPredicate fOfA gOfA
                                    , makeEqualsPredicate gOfA gOfB
                                    ]
                            , substitution =
                                Substitution.unsafeWrap $
                                    List.sortOn
                                        fst
                                        [ (inject z', gOfB)
                                        , (inject Mock.xConfig, fOfA)
                                        , (inject Mock.yConfig, gOfA)
                                        ]
                            }
                        ]
            actuals <-
                let result :: AttemptedAxiom RewritingVariableName
                    result =
                        AttemptedAxiom.Applied
                            AttemptedAxiomResults
                                { results =
                                    OrPattern.fromPatterns
                                        [ Conditional
                                            { term = fOfA
                                            , predicate = makeEqualsPredicate fOfA gOfA
                                            , substitution =
                                                Substitution.wrap $
                                                    Substitution.mkUnwrappedSubstitution
                                                        [(inject z', gOfB)]
                                            }
                                        ]
                                , remainders = OrPattern.fromPatterns []
                                }
                 in evaluate
                        ( Map.singleton
                            (AxiomIdentifier.Application Mock.sigmaId)
                            ( simplificationEvaluator
                                [ BuiltinAndAxiomSimplifier $ \_ _ ->
                                    return result
                                ]
                            )
                        )
                        ( makeApplication
                            Mock.sigmaSymbol
                            [
                                [ Conditional
                                    { term = Mock.a
                                    , predicate = makeEqualsPredicate fOfA fOfB
                                    , substitution =
                                        Substitution.wrap $
                                            Substitution.mkUnwrappedSubstitution
                                                [(inject Mock.xConfig, fOfA)]
                                    }
                                ]
                            ,
                                [ Conditional
                                    { term = Mock.b
                                    , predicate = makeEqualsPredicate gOfA gOfB
                                    , substitution =
                                        Substitution.wrap $
                                            Substitution.mkUnwrappedSubstitution
                                                [(inject Mock.yConfig, gOfA)]
                                    }
                                ]
                            ]
                        )
            Pattern.assertEquivalentPatterns expects actuals
        ]
    ]
  where
    fOfA, fOfB, gOfA, gOfB :: TermLike RewritingVariableName
    fOfA = Mock.f Mock.a
    fOfB = Mock.f Mock.b
    gOfA = Mock.g Mock.a
    gOfB = Mock.g Mock.b

    aExpanded =
        Conditional
            { term = Mock.a
            , predicate = makeTruePredicate
            , substitution = mempty
            }
    bExpanded =
        Conditional
            { term = Mock.b
            , predicate = makeTruePredicate
            , substitution = mempty
            }
    cExpanded =
        Conditional
            { term = Mock.c
            , predicate = makeTruePredicate
            , substitution = mempty
            }
    dExpanded =
        Conditional
            { term = Mock.d
            , predicate = makeTruePredicate
            , substitution = mempty
            }

    gOfAExpanded :: Pattern RewritingVariableName
    gOfAExpanded =
        Conditional
            { term = gOfA
            , predicate = makeTruePredicate
            , substitution = mempty
            }

simplificationEvaluator ::
    [BuiltinAndAxiomSimplifier] ->
    BuiltinAndAxiomSimplifier
simplificationEvaluator = firstFullEvaluation

makeApplication ::
    Symbol ->
    [[Pattern RewritingVariableName]] ->
    Application Symbol (OrPattern RewritingVariableName)
makeApplication symbol patterns =
    Application
        { applicationSymbolOrAlias = symbol
        , applicationChildren = map OrPattern.fromPatterns patterns
        }

evaluate ::
    -- | Map from axiom IDs to axiom evaluators
    BuiltinAndAxiomSimplifierMap ->
    Application Symbol (OrPattern RewritingVariableName) ->
    IO (OrPattern RewritingVariableName)
evaluate simplifierAxioms = runSimplifier mockEnv . simplify SideCondition.top
  where
    mockEnv = Mock.env{simplifierAxioms}
