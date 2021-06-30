{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Test.Kore.Rewrite.Function.Integration (
    test_functionIntegration,
    test_functionIntegrationUnification,
    test_Nat,
    test_NatUnification,
    test_short_circuit,
    test_List,
    test_lookupMap,
    test_updateMap,
    test_updateList,
    test_Ceil,
) where

import qualified Control.Lens as Lens
import Data.Generics.Product
import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import Data.Sup
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin as Builtin
import qualified Kore.Builtin.AssociativeCommutative as Ac
import qualified Kore.Builtin.Int as Int (
    builtinFunctions,
 )
import qualified Kore.Builtin.Map as Map (
    builtinFunctions,
 )
import Kore.Equation
import qualified Kore.Error
import Kore.IndexedModule.IndexedModule as IndexedModule
import Kore.IndexedModule.MetadataTools (
    SmtMetadataTools,
 )
import qualified Kore.IndexedModule.MetadataToolsBuilder as MetadataTools
import qualified Kore.IndexedModule.SortGraph as SortGraph
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
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
    top,
 )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.Symbol
import Kore.Internal.TermLike
import Kore.Rewrite.Axiom.EvaluationStrategy (
    builtinEvaluation,
    definitionEvaluation,
    firstFullEvaluation,
    simplificationEvaluation,
    simplifierWithFallback,
 )
import Kore.Rewrite.Axiom.Identifier (
    AxiomIdentifier,
 )
import qualified Kore.Rewrite.Axiom.Identifier as AxiomIdentifier
import qualified Kore.Rewrite.Function.Memo as Memo
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    configElementVariableFromId,
    mkConfigVariable,
 )
import qualified Kore.Simplify.Condition as Simplifier.Condition
import Kore.Simplify.InjSimplifier (
    InjSimplifier,
    mkInjSimplifier,
 )
import Kore.Simplify.Simplify
import Kore.Simplify.Simplify as AttemptedAxiom (
    AttemptedAxiom (..),
 )
import qualified Kore.Simplify.SubstitutionSimplifier as SubstitutionSimplifier
import qualified Kore.Simplify.TermLike as TermLike
import Kore.Syntax.Definition hiding (
    Symbol (..),
 )
import Kore.Unparser
import Kore.Validate.DefinitionVerifier
import Kore.Validate.Error (
    VerifyError,
 )
import Prelude.Kore hiding (
    succ,
 )
import qualified Pretty
import Test.Kore
import qualified Test.Kore.Builtin.Bool as Bool
import qualified Test.Kore.Builtin.Builtin as Builtin
import qualified Test.Kore.Builtin.Definition as Builtin
import qualified Test.Kore.Builtin.Int as Int
import qualified Test.Kore.Builtin.List as List
import qualified Test.Kore.Builtin.Map as Map
import Test.Kore.Equation.Common (
    axiom,
    axiom_,
    functionAxiomUnification,
    functionAxiomUnification_,
 )
import Test.Kore.Rewrite.Axiom.Matcher (
    doesn'tMatch,
    matches,
 )
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Kore.Simplify
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_functionIntegration :: [TestTree]
test_functionIntegration =
    [ testCase "Simple evaluation" $ do
        let expect = Mock.g Mock.c
        actual <-
            evaluate
                ( Map.singleton
                    (AxiomIdentifier.Application Mock.functional10Id)
                    ( axiomEvaluator
                        (Mock.functional10 (mkElemVar Mock.xConfig))
                        (Mock.g (mkElemVar Mock.xConfig))
                    )
                )
                (Mock.functional10 Mock.c)
        assertEqual "" expect (OrPattern.toTermLike actual)
    , testCase "Simple evaluation (builtin branch)" $ do
        let expect = Mock.g Mock.c
        actual <-
            evaluate
                ( Map.singleton
                    (AxiomIdentifier.Application Mock.functional10Id)
                    ( builtinEvaluation $
                        axiomEvaluator
                            (Mock.functional10 (mkElemVar Mock.xConfig))
                            (Mock.g (mkElemVar Mock.xConfig))
                    )
                )
                (Mock.functional10 Mock.c)
        assertEqual "" expect (OrPattern.toTermLike actual)
    , testCase "Simple evaluation (Axioms & Builtin branch, Builtin works)" $
        do
            let expect = Mock.g Mock.c
            actual <-
                evaluate
                    ( Map.singleton
                        (AxiomIdentifier.Application Mock.functional10Id)
                        ( simplifierWithFallback
                            ( builtinEvaluation $
                                axiomEvaluator
                                    (Mock.functional10 (mkElemVar Mock.xConfig))
                                    (Mock.g (mkElemVar Mock.xConfig))
                            )
                            ( axiomEvaluator
                                (Mock.functional10 (mkElemVar Mock.xConfig))
                                (mkElemVar Mock.xConfig)
                            )
                        )
                    )
                    (Mock.functional10 Mock.c)
            assertEqual "" expect (OrPattern.toTermLike actual)
    , testCase "Simple evaluation (Axioms & Builtin branch, Builtin fails)" $
        do
            let expect = Mock.g Mock.c
            actual <-
                evaluate
                    ( Map.singleton
                        (AxiomIdentifier.Application Mock.functional10Id)
                        ( simplifierWithFallback
                            ( builtinEvaluation $
                                BuiltinAndAxiomSimplifier $ \_ _ ->
                                    notApplicableAxiomEvaluator
                            )
                            ( axiomEvaluator
                                (Mock.functional10 (mkElemVar Mock.xConfig))
                                (Mock.g (mkElemVar Mock.xConfig))
                            )
                        )
                    )
                    (Mock.functional10 Mock.c)
            assertEqual "" expect (OrPattern.toTermLike actual)
    , testCase "Evaluates inside functions" $ do
        let expect = Mock.functional11 (Mock.functional11 Mock.c)
        actual <-
            evaluate
                ( Map.singleton
                    (AxiomIdentifier.Application Mock.functional10Id)
                    ( axiomEvaluator
                        (Mock.functional10 (mkElemVar Mock.xConfig))
                        (Mock.functional11 (mkElemVar Mock.xConfig))
                    )
                )
                (Mock.functional10 (Mock.functional10 Mock.c))
        assertEqual "" expect (OrPattern.toTermLike actual)
    , testCase "Evaluates 'or'" $ do
        let expect =
                mkOr
                    (Mock.functional11 (Mock.functional11 Mock.c))
                    (Mock.functional11 (Mock.functional11 Mock.d))
        actual <-
            evaluate
                ( Map.singleton
                    (AxiomIdentifier.Application Mock.functional10Id)
                    ( axiomEvaluator
                        (Mock.functional10 (mkElemVar Mock.xConfig))
                        (Mock.functional11 (mkElemVar Mock.xConfig))
                    )
                )
                ( Mock.functional10
                    ( mkOr
                        (Mock.functional10 Mock.c)
                        (Mock.functional10 Mock.d)
                    )
                )
        assertEqual "" expect (OrPattern.toTermLike actual)
    , testCase "Evaluates on multiple branches" $ do
        let expect =
                Mock.functional11
                    ( Mock.functional20
                        (Mock.functional11 Mock.c)
                        (Mock.functional11 Mock.c)
                    )
        actual <-
            evaluate
                ( Map.singleton
                    (AxiomIdentifier.Application Mock.functional10Id)
                    ( axiomEvaluator
                        (Mock.functional10 (mkElemVar Mock.xConfig))
                        (Mock.functional11 (mkElemVar Mock.xConfig))
                    )
                )
                ( Mock.functional10
                    ( Mock.functional20
                        (Mock.functional10 Mock.c)
                        (Mock.functional10 Mock.c)
                    )
                )
        assertEqual "" expect (OrPattern.toTermLike actual)
    , testCase "Returns conditions" $ do
        let expect =
                Conditional
                    { term = Mock.f Mock.d
                    , predicate =
                        makeCeilPredicate
                            (Mock.plain10 Mock.e)
                    , substitution = mempty
                    }
        actual <-
            evaluate
                ( Map.singleton
                    (AxiomIdentifier.Application Mock.cfId)
                    ( appliedMockEvaluator
                        Conditional
                            { term = Mock.d
                            , predicate =
                                makeCeilPredicate
                                    (Mock.plain10 Mock.e)
                            , substitution = mempty
                            }
                    )
                )
                (Mock.f Mock.cf)
        assertEqual "" (MultiOr.singleton expect) actual
    , testCase "Merges conditions" $ do
        let expect =
                Conditional
                    { term = Mock.functional11 (Mock.functional20 Mock.e Mock.e)
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate (Mock.f Mock.a))
                            (makeCeilPredicate (Mock.g Mock.a))
                    , substitution = mempty
                    }
        actual <-
            evaluate
                ( Map.fromList
                    [
                        ( AxiomIdentifier.Application Mock.cfId
                        , appliedMockEvaluator
                            Conditional
                                { term = Mock.e
                                , predicate = makeCeilPredicate (Mock.g Mock.a)
                                , substitution = mempty
                                }
                        )
                    ,
                        ( AxiomIdentifier.Application Mock.cgId
                        , appliedMockEvaluator
                            Conditional
                                { term = Mock.e
                                , predicate = makeCeilPredicate (Mock.f Mock.a)
                                , substitution = mempty
                                }
                        )
                    ,
                        ( AxiomIdentifier.Application Mock.functional10Id
                        , axiomEvaluator
                            (Mock.functional10 (mkElemVar Mock.xConfig))
                            (Mock.functional11 (mkElemVar Mock.xConfig))
                        )
                    ]
                )
                (Mock.functional10 (Mock.functional20 Mock.cf Mock.cg))
        assertEqual "" (MultiOr.singleton expect) actual
    , testCase "Reevaluates user-defined function results." $ do
        let expect =
                Conditional
                    { term = Mock.f Mock.e
                    , predicate =
                        makeEqualsPredicate
                            Mock.e
                            (Mock.f Mock.e)
                    , substitution = mempty
                    }
        actual <-
            evaluate
                ( Map.fromList
                    [
                        ( AxiomIdentifier.Application Mock.cfId
                        , axiomEvaluator Mock.cf Mock.cg
                        )
                    ,
                        ( AxiomIdentifier.Application Mock.cgId
                        , appliedMockEvaluator
                            Conditional
                                { term = Mock.e
                                , predicate =
                                    makeEqualsPredicate (Mock.f Mock.e) Mock.e
                                , substitution = mempty
                                }
                        )
                    ]
                )
                (Mock.f Mock.cf)
        assertEqual "" (MultiOr.singleton expect) actual
    , testCase "Merges substitutions with reevaluation ones." $ do
        let expect =
                Conditional
                    { term = Mock.f Mock.e
                    , predicate = makeTruePredicate
                    , substitution =
                        Substitution.unsafeWrap
                            [
                                ( inject Mock.var_xConfig_1
                                , Mock.a
                                )
                            ,
                                ( inject Mock.var_zConfig_1
                                , Mock.a
                                )
                            ]
                    }
        actual <-
            evaluate
                ( Map.fromList
                    [
                        ( AxiomIdentifier.Application Mock.cfId
                        , appliedMockEvaluator
                            Conditional
                                { term = Mock.cg
                                , predicate = makeTruePredicate
                                , substitution =
                                    Substitution.unsafeWrap
                                        [
                                            ( inject Mock.x
                                            , mkElemVar Mock.z
                                            )
                                        ]
                                }
                        )
                    ,
                        ( AxiomIdentifier.Application Mock.cgId
                        , appliedMockEvaluator
                            Conditional
                                { term = Mock.e
                                , predicate = makeTruePredicate
                                , substitution =
                                    Substitution.unsafeWrap
                                        [
                                            ( inject Mock.x
                                            , Mock.a
                                            )
                                        ]
                                }
                        )
                    ]
                )
                (Mock.f Mock.cf)
        assertEqual "" (MultiOr.singleton expect) actual
    , testCase "Simplifies substitution-predicate." $ do
        -- Mock.plain10 below prevents:
        -- 1. unification without substitution.
        -- 2. Transforming the 'and' in an equals predicate,
        --    as it would happen for functions.
        let expect =
                Conditional
                    { term = Mock.a
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate Mock.cf)
                            ( makeCeilPredicate
                                (Mock.plain10 Mock.cf)
                            )
                    , substitution =
                        Substitution.unsafeWrap
                            [ (inject Mock.var_xConfig_1, Mock.cf)
                            , (inject Mock.var_yConfig_1, Mock.b)
                            ]
                    }
        actual <-
            evaluate
                ( Map.fromList
                    [
                        ( AxiomIdentifier.Application Mock.fId
                        , appliedMockEvaluator
                            Conditional
                                { term = Mock.a
                                , predicate =
                                    makeCeilPredicate
                                        ( mkAnd
                                            ( Mock.constr20
                                                (Mock.plain10 Mock.cf)
                                                Mock.b
                                            )
                                            ( Mock.constr20
                                                (Mock.plain10 (mkElemVar Mock.x))
                                                (mkElemVar Mock.y)
                                            )
                                        )
                                , substitution =
                                    Substitution.wrap $
                                        Substitution.mkUnwrappedSubstitution
                                            [(inject Mock.x, Mock.cf)]
                                }
                        )
                    ]
                )
                (Mock.f (mkElemVar Mock.xConfig))
        let message =
                (show . Pretty.vsep)
                    [ "Expected:"
                    , Pretty.indent 4 (unparse expect)
                    , "but found:"
                    , Pretty.indent 4 (unparse $ OrPattern.toTermLike actual)
                    ]
        assertEqual message (MultiOr.singleton expect) actual
    , testCase "Evaluates only simplifications." $ do
        let expect =
                Conditional
                    { term = Mock.b
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                ( Map.fromList
                    [
                        ( AxiomIdentifier.Application Mock.fId
                        , simplifierWithFallback
                            (appliedMockEvaluator (Pattern.fromTermLike Mock.b))
                            ( definitionEvaluation
                                [axiom_ (Mock.f (mkElemVar Mock.yConfig)) Mock.a]
                            )
                        )
                    ]
                )
                (Mock.f (mkElemVar Mock.xConfig))
        assertEqual "" (MultiOr.singleton expect) actual
    , testCase "Picks first matching simplification." $ do
        let expect =
                Conditional
                    { term = Mock.b
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                ( Map.fromList
                    [
                        ( AxiomIdentifier.Application Mock.fId
                        , simplifierWithFallback
                            ( firstFullEvaluation
                                [ axiomEvaluator
                                    (Mock.f (Mock.g (mkElemVar Mock.xConfig)))
                                    Mock.c
                                , appliedMockEvaluator
                                    Conditional
                                        { term = Mock.b
                                        , predicate = makeTruePredicate
                                        , substitution = mempty
                                        }
                                , appliedMockEvaluator
                                    Conditional
                                        { term = Mock.c
                                        , predicate = makeTruePredicate
                                        , substitution = mempty
                                        }
                                ]
                            )
                            ( definitionEvaluation
                                [ axiom
                                    (Mock.f (mkElemVar Mock.yConfig))
                                    Mock.a
                                    makeTruePredicate
                                ]
                            )
                        )
                    ]
                )
                (Mock.f (mkElemVar Mock.xConfig))
        assertEqual "" (MultiOr.singleton expect) actual
    , testCase "Falls back to evaluating the definition." $ do
        let expect =
                Conditional
                    { term = Mock.a
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                ( Map.fromList
                    [
                        ( AxiomIdentifier.Application Mock.fId
                        , simplifierWithFallback
                            ( axiomEvaluator
                                (Mock.f (Mock.g (mkElemVar Mock.xConfig)))
                                Mock.b
                            )
                            ( definitionEvaluation
                                [ axiom
                                    (Mock.f (mkElemVar Mock.yConfig))
                                    Mock.a
                                    makeTruePredicate
                                ]
                            )
                        )
                    ]
                )
                (Mock.f (mkElemVar Mock.xConfig))
        assertEqual "" (MultiOr.singleton expect) actual
        {-
            Uncomment this if we ever go back to allowing branches for function
            evaluation.

            , testCase "Multiple definition branches." $ do
                let expect =
                        Pattern.fromTermLike $ mkOr
                            (mkAnd Mock.a (mkCeil Mock.testSort Mock.cf))
                            (mkAnd Mock.b (mkNot (mkCeil Mock.testSort Mock.cf)))
                actual <-
                    evaluate
                        (Map.fromList
                            [   ( AxiomIdentifier.Application Mock.fId
                                , simplifierWithFallback
                                    (axiomEvaluator
                                        (Mock.f (Mock.g (mkElemVar Mock.x)))
                                        Mock.c
                                    )
                                    (definitionEvaluation
                                        [ axiom
                                            (Mock.f (mkElemVar Mock.y))
                                            Mock.a
                                            (makeCeilPredicate Mock.cf)
                                        , axiom_ (Mock.f (mkElemVar Mock.y)) Mock.b
                                        ]
                                    )
                                )
                            ]
                        )
                        (Mock.f (mkElemVar Mock.x))
                assertEqual "" expect actual-}
    ]

test_functionIntegrationUnification :: [TestTree]
test_functionIntegrationUnification =
    [ testCase "Simple evaluation" $ do
        let expect =
                Conditional
                    { term = Mock.g Mock.c
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                ( Map.singleton
                    (AxiomIdentifier.Application Mock.functional10Id)
                    ( axiomEvaluatorUnification
                        Mock.functional10Symbol
                        [mkElemVar Mock.xConfig]
                        (Mock.g (mkElemVar Mock.xConfig))
                    )
                )
                (Mock.functional10 Mock.c)
        assertEqual "" (MultiOr.singleton expect) actual
    , testCase "Simple evaluation (builtin branch)" $ do
        let expect =
                Conditional
                    { term = Mock.g Mock.c
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                ( Map.singleton
                    (AxiomIdentifier.Application Mock.functional10Id)
                    ( builtinEvaluation $
                        axiomEvaluatorUnification
                            Mock.functional10Symbol
                            [mkElemVar Mock.xConfig]
                            (Mock.g (mkElemVar Mock.xConfig))
                    )
                )
                (Mock.functional10 Mock.c)
        assertEqual "" (MultiOr.singleton expect) actual
    , testCase "Simple evaluation (Axioms & Builtin branch, Builtin works)" $
        do
            let expect =
                    Conditional
                        { term = Mock.g Mock.c
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            actual <-
                evaluate
                    ( Map.singleton
                        (AxiomIdentifier.Application Mock.functional10Id)
                        ( simplifierWithFallback
                            ( builtinEvaluation $
                                axiomEvaluatorUnification
                                    Mock.functional10Symbol
                                    [mkElemVar Mock.xConfig]
                                    (Mock.g (mkElemVar Mock.xConfig))
                            )
                            ( axiomEvaluatorUnification
                                Mock.functional10Symbol
                                [mkElemVar Mock.xConfig]
                                (mkElemVar Mock.xConfig)
                            )
                        )
                    )
                    (Mock.functional10 Mock.c)
            assertEqual "" (MultiOr.singleton expect) actual
    , testCase "Simple evaluation (Axioms & Builtin branch, Builtin fails)" $
        do
            let expect =
                    Conditional
                        { term = Mock.g Mock.c
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            actual <-
                evaluate
                    ( Map.singleton
                        (AxiomIdentifier.Application Mock.functional10Id)
                        ( simplifierWithFallback
                            ( builtinEvaluation $
                                BuiltinAndAxiomSimplifier $ \_ _ ->
                                    notApplicableAxiomEvaluator
                            )
                            ( axiomEvaluatorUnification
                                Mock.functional10Symbol
                                [mkElemVar Mock.xConfig]
                                (Mock.g (mkElemVar Mock.xConfig))
                            )
                        )
                    )
                    (Mock.functional10 Mock.c)
            assertEqual "" (MultiOr.singleton expect) actual
    , testCase "Evaluates inside functions" $ do
        let expect =
                Conditional
                    { term = Mock.functional11 (Mock.functional11 Mock.c)
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                ( Map.singleton
                    (AxiomIdentifier.Application Mock.functional10Id)
                    ( axiomEvaluatorUnification
                        Mock.functional10Symbol
                        [mkElemVar Mock.xConfig]
                        (Mock.functional11 (mkElemVar Mock.xConfig))
                    )
                )
                (Mock.functional10 (Mock.functional10 Mock.c))
        assertEqual "" (MultiOr.singleton expect) actual
    , testCase "Evaluates 'or'" $ do
        let expect =
                MultiOr.make
                    [ Conditional
                        { term = Mock.functional11 (Mock.functional11 Mock.c)
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    , Conditional
                        { term = Mock.functional11 (Mock.functional11 Mock.d)
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]

        actual <-
            evaluate
                ( Map.singleton
                    (AxiomIdentifier.Application Mock.functional10Id)
                    ( axiomEvaluatorUnification
                        Mock.functional10Symbol
                        [mkElemVar Mock.xConfig]
                        (Mock.functional11 (mkElemVar Mock.xConfig))
                    )
                )
                ( Mock.functional10
                    ( mkOr
                        (Mock.functional10 Mock.c)
                        (Mock.functional10 Mock.d)
                    )
                )
        assertEqual "" expect actual
    , testCase "Evaluates on multiple branches" $ do
        let expect =
                Conditional
                    { term =
                        Mock.functional11
                            ( Mock.functional20
                                (Mock.functional11 Mock.c)
                                (Mock.functional11 Mock.c)
                            )
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                ( Map.singleton
                    (AxiomIdentifier.Application Mock.functional10Id)
                    ( axiomEvaluatorUnification
                        Mock.functional10Symbol
                        [mkElemVar Mock.xConfig]
                        (Mock.functional11 (mkElemVar Mock.xConfig))
                    )
                )
                ( Mock.functional10
                    ( Mock.functional20
                        (Mock.functional10 Mock.c)
                        (Mock.functional10 Mock.c)
                    )
                )
        assertEqual "" (MultiOr.singleton expect) actual
    , testCase "Merges conditions" $ do
        let expect =
                Conditional
                    { term = Mock.functional11 (Mock.functional20 Mock.e Mock.e)
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate (Mock.f Mock.a))
                            (makeCeilPredicate (Mock.g Mock.a))
                    , substitution = mempty
                    }
        actual <-
            evaluate
                ( Map.fromList
                    [
                        ( AxiomIdentifier.Application Mock.cfId
                        , appliedMockEvaluator
                            Conditional
                                { term = Mock.e
                                , predicate = makeCeilPredicate (Mock.g Mock.a)
                                , substitution = mempty
                                }
                        )
                    ,
                        ( AxiomIdentifier.Application Mock.cgId
                        , appliedMockEvaluator
                            Conditional
                                { term = Mock.e
                                , predicate = makeCeilPredicate (Mock.f Mock.a)
                                , substitution = mempty
                                }
                        )
                    ,
                        ( AxiomIdentifier.Application Mock.functional10Id
                        , axiomEvaluatorUnification
                            Mock.functional10Symbol
                            [mkElemVar Mock.xConfig]
                            (Mock.functional11 (mkElemVar Mock.xConfig))
                        )
                    ]
                )
                (Mock.functional10 (Mock.functional20 Mock.cf Mock.cg))
        assertEqual "" (MultiOr.singleton expect) actual
    , testCase "Reevaluates user-defined function results." $ do
        let expect =
                Conditional
                    { term = Mock.f Mock.e
                    , predicate =
                        makeEqualsPredicate
                            Mock.e
                            (Mock.f Mock.e)
                    , substitution = mempty
                    }
        actual <-
            evaluate
                ( Map.fromList
                    [
                        ( AxiomIdentifier.Application Mock.cfId
                        , axiomEvaluatorUnification Mock.cfSymbol [] Mock.cg
                        )
                    ,
                        ( AxiomIdentifier.Application Mock.cgId
                        , appliedMockEvaluator
                            Conditional
                                { term = Mock.e
                                , predicate =
                                    makeEqualsPredicate (Mock.f Mock.e) Mock.e
                                , substitution = mempty
                                }
                        )
                    ]
                )
                (Mock.f Mock.cf)
        assertEqual "" (MultiOr.singleton expect) actual
    , testCase "Evaluates only simplifications." $ do
        let expect =
                Conditional
                    { term = Mock.b
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                ( Map.fromList
                    [
                        ( AxiomIdentifier.Application Mock.fId
                        , simplifierWithFallback
                            (appliedMockEvaluator (Pattern.fromTermLike Mock.b))
                            ( definitionEvaluation
                                [ functionAxiomUnification_
                                    Mock.fSymbol
                                    [mkElemVar Mock.yConfig]
                                    Mock.a
                                ]
                            )
                        )
                    ]
                )
                (Mock.f (mkElemVar Mock.xConfig))
        assertEqual "" (MultiOr.singleton expect) actual
    , testCase "Picks first matching simplification." $ do
        let expect =
                Conditional
                    { term = Mock.b
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                ( Map.fromList
                    [
                        ( AxiomIdentifier.Application Mock.fId
                        , simplifierWithFallback
                            ( firstFullEvaluation
                                [ axiomEvaluatorUnification
                                    Mock.fSymbol
                                    [Mock.g (mkElemVar Mock.xConfig)]
                                    Mock.c
                                , appliedMockEvaluator
                                    Conditional
                                        { term = Mock.b
                                        , predicate = makeTruePredicate
                                        , substitution = mempty
                                        }
                                , appliedMockEvaluator
                                    Conditional
                                        { term = Mock.c
                                        , predicate = makeTruePredicate
                                        , substitution = mempty
                                        }
                                ]
                            )
                            ( definitionEvaluation
                                [ functionAxiomUnification
                                    Mock.fSymbol
                                    [mkElemVar Mock.yConfig]
                                    Mock.a
                                    makeTruePredicate
                                ]
                            )
                        )
                    ]
                )
                (Mock.f (mkElemVar Mock.xConfig))
        assertEqual "" (MultiOr.singleton expect) actual
    , testCase "Falls back to evaluating the definition." $ do
        let expect =
                Conditional
                    { term = Mock.a
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                ( Map.fromList
                    [
                        ( AxiomIdentifier.Application Mock.fId
                        , simplifierWithFallback
                            ( axiomEvaluatorUnification
                                Mock.fSymbol
                                [Mock.g (mkElemVar Mock.xConfig)]
                                Mock.b
                            )
                            ( definitionEvaluation
                                [ functionAxiomUnification
                                    Mock.fSymbol
                                    [mkElemVar Mock.yConfig]
                                    Mock.a
                                    makeTruePredicate
                                ]
                            )
                        )
                    ]
                )
                (Mock.f (mkElemVar Mock.xConfig))
        assertEqual "" (MultiOr.singleton expect) actual
    ]

test_Nat :: [TestTree]
test_Nat =
    [ matches
        "plus(0, N) matches plus(0, 1)"
        (plus zero varNConfig)
        (plus zero one)
        [(inject natNConfig, one)]
    , doesn'tMatch
        "plus(succ(M), N) doesn't match plus(0, 1)"
        (plus (succ varMConfig) varNConfig)
        (plus zero one)
    , matches
        "plus(succ(M), N) matches plus(1, 1)"
        (plus (succ varMConfig) varNConfig)
        (plus one one)
        [(inject natMConfig, zero), (inject natNConfig, one)]
    , applies
        "plus(0, N) => ... ~ plus (0, 1)"
        [plusZeroRule]
        (plus zero one)
    , notApplies
        "plus(0, N) => ... ~ plus (1, 1)"
        [plusZeroRule]
        (plus one one)
    , notApplies
        "plus(Succ(M), N) => ... ~ plus (0, 1)"
        [plusSuccRule]
        (plus zero one)
    , applies
        "plus(Succ(M), N) => ... ~ plus (1, 1)"
        [plusSuccRule]
        (plus one one)
    , applies
        "plus(0, 1) => ..."
        plusRules
        (plus zero one)
    , applies
        "plus(1, 1) => ..."
        plusRules
        (plus one one)
    , equals "0 + 1 = 1 : Nat" (plus zero one) [one]
    , equals "0 + 1 = 1 : Nat" (plus one one) [two]
    , equals "0 * 1 = 0 : Nat" (times zero one) [zero]
    , equals "1 * 1 = 1 : Nat" (times one one) [one]
    , equals "1 * 2 = 2 : Nat" (times one two) [two]
    , equals "2 * 1 = 2 : Nat" (times two one) [two]
    , equals "0! = 1 : Nat" (factorial zero) [one]
    , equals "1! = 1 : Nat" (factorial one) [one]
    , equals "2! = 2 : Nat" (factorial two) [two]
    , equals "fibonacci(0) = 1 : Nat" (fibonacci zero) [one]
    , equals "fibonacci(1) = 1 : Nat" (fibonacci one) [one]
    , equals "fibonacci(2) = 2 : Nat" (fibonacci two) [two]
    ]

test_NatUnification :: [TestTree]
test_NatUnification =
    [ matches
        "plus(0, N) matches plus(0, 1)"
        (plus zero varNConfig)
        (plus zero one)
        [(inject natNConfig, one)]
    , doesn'tMatch
        "plus(succ(M), N) doesn't match plus(0, 1)"
        (plus (succ varMConfig) varNConfig)
        (plus zero one)
    , matches
        "plus(succ(M), N) matches plus(1, 1)"
        (plus (succ varMConfig) varNConfig)
        (plus one one)
        [(inject natMConfig, zero), (inject natNConfig, one)]
    , appliesUnification
        "plus(0, N) => ... ~ plus (0, 1)"
        [plusZeroRule]
        (plus zero one)
    , notAppliesUnification
        "plus(0, N) => ... ~ plus (1, 1)"
        [plusZeroRule]
        (plus one one)
    , notAppliesUnification
        "plus(Succ(M), N) => ... ~ plus (0, 1)"
        [plusSuccRule]
        (plus zero one)
    , appliesUnification
        "plus(Succ(M), N) => ... ~ plus (1, 1)"
        [plusSuccRule]
        (plus one one)
    , appliesUnification
        "plus(0, 1) => ..."
        plusRules
        (plus zero one)
    , appliesUnification
        "plus(1, 1) => ..."
        plusRules
        (plus one one)
    , equalsUnification "0 + 1 = 1 : Nat" (plus zero one) [one]
    , equalsUnification "0 + 1 = 1 : Nat" (plus one one) [two]
    , equalsUnification "0 * 1 = 0 : Nat" (times zero one) [zero]
    , equalsUnification "1 * 1 = 1 : Nat" (times one one) [one]
    , equalsUnification "1 * 2 = 2 : Nat" (times one two) [two]
    , equalsUnification "2 * 1 = 2 : Nat" (times two one) [two]
    , equalsUnification "0! = 1 : Nat" (factorial zero) [one]
    , equalsUnification "1! = 1 : Nat" (factorial one) [one]
    , equalsUnification "2! = 2 : Nat" (factorial two) [two]
    , equalsUnification "fibonacci(0) = 1 : Nat" (fibonacci zero) [one]
    , equalsUnification "fibonacci(1) = 1 : Nat" (fibonacci one) [one]
    , equalsUnification "fibonacci(2) = 2 : Nat" (fibonacci two) [two]
    ]

-- Evaluation tests: check the result of evaluating the term
equals ::
    HasCallStack =>
    TestName ->
    TermLike RewritingVariableName ->
    [TermLike RewritingVariableName] ->
    TestTree
equals comment term results =
    testCase comment $ do
        actual <- simplify term
        let expect = OrPattern.fromPatterns $ Pattern.fromTermLike <$> results
        assertEqual "" expect actual

equalsUnification ::
    HasCallStack =>
    TestName ->
    TermLike RewritingVariableName ->
    [TermLike RewritingVariableName] ->
    TestTree
equalsUnification comment term results =
    testCase comment $ do
        actual <- simplifyUnification term
        let expect = OrPattern.fromPatterns $ Pattern.fromTermLike <$> results
        assertEqual "" expect actual

simplify ::
    TermLike RewritingVariableName -> IO (OrPattern RewritingVariableName)
simplify = runSimplifier testEnv . TermLike.simplify SideCondition.top

simplifyUnification ::
    TermLike RewritingVariableName -> IO (OrPattern RewritingVariableName)
simplifyUnification = runSimplifier testEnvUnification . TermLike.simplify SideCondition.top

evaluate ::
    BuiltinAndAxiomSimplifierMap ->
    TermLike RewritingVariableName ->
    IO (OrPattern RewritingVariableName)
evaluate functionIdToEvaluator termLike =
    runSimplifier Mock.env{simplifierAxioms = functionIdToEvaluator} $
        TermLike.simplify SideCondition.top termLike

evaluateWith ::
    BuiltinAndAxiomSimplifier ->
    TermLike RewritingVariableName ->
    IO CommonAttemptedAxiom
evaluateWith simplifier patt =
    runSimplifierSMT testEnv $
        runBuiltinAndAxiomSimplifier simplifier patt SideCondition.top

evaluateWithUnification ::
    BuiltinAndAxiomSimplifier ->
    TermLike RewritingVariableName ->
    IO CommonAttemptedAxiom
evaluateWithUnification simplifier patt =
    runSimplifier testEnvUnification $
        runBuiltinAndAxiomSimplifier simplifier patt SideCondition.top

-- Applied tests: check that one or more rules applies or not
withApplied ::
    (CommonAttemptedAxiom -> Assertion) ->
    TestName ->
    [Equation RewritingVariableName] ->
    TermLike RewritingVariableName ->
    TestTree
withApplied check comment rules term =
    testCase comment $ do
        actual <- evaluateWith (definitionEvaluation rules) term
        check actual

withAppliedUnification ::
    (CommonAttemptedAxiom -> Assertion) ->
    TestName ->
    [Equation RewritingVariableName] ->
    TermLike RewritingVariableName ->
    TestTree
withAppliedUnification check comment rules term =
    testCase comment $ do
        actual <- evaluateWithUnification (definitionEvaluation rules) term
        check actual

applies
    , notApplies
    , appliesUnification
    , notAppliesUnification ::
        TestName ->
        [Equation RewritingVariableName] ->
        TermLike RewritingVariableName ->
        TestTree
applies =
    withApplied $ \attempted -> do
        results <- expectApplied attempted
        expectNoRemainders results
  where
    expectApplied NotApplicable = assertFailure "Expected Applied"
    expectApplied (NotApplicableUntilConditionChanges _) =
        assertFailure "Expected Applied"
    expectApplied (Applied results) = return results
    expectNoRemainders =
        assertBool "Expected no remainders"
            . isBottom
            . Lens.view (field @"remainders")
notApplies =
    withApplied $ \r ->
        assertBool "Expected NotApplicable" $
            isNotApplicable r || isNotApplicableUntilConditionChanges r
appliesUnification =
    withAppliedUnification $ \attempted -> do
        results <- expectApplied attempted
        expectNoRemainders results
  where
    expectApplied NotApplicable = assertFailure "Expected Applied"
    expectApplied (NotApplicableUntilConditionChanges _) =
        assertFailure "Expected Applied"
    expectApplied (Applied results) = return results
    expectNoRemainders =
        assertBool "Expected no remainders"
            . isBottom
            . Lens.view (field @"remainders")
notAppliesUnification =
    withAppliedUnification $ \r ->
        assertBool "Expected NotApplicable" $
            isNotApplicable r || isNotApplicableUntilConditionChanges r

natSort :: Sort
natSort =
    SortActualSort
        SortActual
            { sortActualName = testId "Nat"
            , sortActualSorts = []
            }

natMConfig
    , natNConfig ::
        ElementVariable RewritingVariableName
natMConfig = configElementVariableFromId "M" natSort
natNConfig = configElementVariableFromId "N" natSort

varMConfig, varNConfig :: TermLike RewritingVariableName
varMConfig = mkElemVar natMConfig
varNConfig = mkElemVar natNConfig

zeroSymbol, succSymbol :: Symbol
zeroSymbol = Mock.symbol "Zero" [] natSort & constructor & functional
succSymbol = Mock.symbol "Succ" [natSort] natSort & constructor & functional

plusSymbol, timesSymbol :: Symbol
plusSymbol = Mock.symbol "plus" [natSort, natSort] natSort & function
timesSymbol = Mock.symbol "times" [natSort, natSort] natSort & function

fibonacciSymbol, factorialSymbol :: Symbol
fibonacciSymbol = Mock.symbol "fibonacci" [natSort] natSort & function
factorialSymbol = Mock.symbol "factorial" [natSort] natSort & function

zero :: TermLike RewritingVariableName
zero = mkApplySymbol zeroSymbol []

one, two :: TermLike RewritingVariableName
one = succ zero
two = succ one

succ
    , fibonacci
    , factorial ::
        TermLike RewritingVariableName -> TermLike RewritingVariableName
succ n = mkApplySymbol succSymbol [n]
fibonacci n = mkApplySymbol fibonacciSymbol [n]
factorial n = mkApplySymbol factorialSymbol [n]

plus
    , times ::
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName
plus n1 n2 = mkApplySymbol plusSymbol [n1, n2]
times n1 n2 = mkApplySymbol timesSymbol [n1, n2]

functionEvaluator ::
    Symbol ->
    -- | Function definition rules
    [Equation RewritingVariableName] ->
    (AxiomIdentifier, BuiltinAndAxiomSimplifier)
functionEvaluator symb rules =
    (AxiomIdentifier.Application ident, definitionEvaluation rules)
  where
    ident = symbolConstructor symb

functionSimplifier ::
    Symbol ->
    -- | Function simplification rule
    [Equation RewritingVariableName] ->
    (AxiomIdentifier, BuiltinAndAxiomSimplifier)
functionSimplifier symb rules =
    ( AxiomIdentifier.Application ident
    , firstFullEvaluation (simplificationEvaluation <$> rules)
    )
  where
    ident = symbolConstructor symb

plusZeroRule, plusSuccRule :: Equation RewritingVariableName
plusZeroRule = axiom_ (plus zero varNConfig) varNConfig
plusSuccRule =
    axiom_ (plus (succ varMConfig) varNConfig) (succ (plus varMConfig varNConfig))

plusRules :: [Equation RewritingVariableName]
plusRules = [plusZeroRule, plusSuccRule]

plusEvaluator :: (AxiomIdentifier, BuiltinAndAxiomSimplifier)
plusEvaluator = functionEvaluator plusSymbol plusRules

timesEvaluator :: (AxiomIdentifier, BuiltinAndAxiomSimplifier)
timesEvaluator =
    functionEvaluator
        timesSymbol
        [ axiom_ (times zero varNConfig) zero
        , axiom_
            (times (succ varMConfig) varNConfig)
            (plus varNConfig (times varMConfig varNConfig))
        ]

fibonacciEvaluator :: (AxiomIdentifier, BuiltinAndAxiomSimplifier)
fibonacciEvaluator =
    functionEvaluator
        fibonacciSymbol
        [ axiom_ (fibonacci zero) one
        , axiom_ (fibonacci one) one
        , axiom_
            (fibonacci (succ (succ varNConfig)))
            (plus (fibonacci (succ varNConfig)) (fibonacci varNConfig))
        ]

factorialEvaluator :: (AxiomIdentifier, BuiltinAndAxiomSimplifier)
factorialEvaluator =
    functionEvaluator
        factorialSymbol
        [ axiom_ (factorial zero) (succ zero)
        , axiom_
            (factorial (succ varNConfig))
            (times (succ varNConfig) (factorial varNConfig))
        ]

natSimplifiers :: BuiltinAndAxiomSimplifierMap
natSimplifiers =
    Map.fromList
        [ plusEvaluator
        , timesEvaluator
        , fibonacciEvaluator
        , factorialEvaluator
        ]

plusZeroRuleUnification
    , plusSuccRuleUnification ::
        Equation RewritingVariableName
plusZeroRuleUnification =
    functionAxiomUnification_ plusSymbol [zero, varNConfig] varNConfig
plusSuccRuleUnification =
    functionAxiomUnification_
        plusSymbol
        [succ varMConfig, varNConfig]
        (succ (plus varMConfig varNConfig))

plusRulesUnification :: [Equation RewritingVariableName]
plusRulesUnification = [plusZeroRuleUnification, plusSuccRuleUnification]

plusEvaluatorUnification :: (AxiomIdentifier, BuiltinAndAxiomSimplifier)
plusEvaluatorUnification = functionEvaluator plusSymbol plusRulesUnification

timesEvaluatorUnification :: (AxiomIdentifier, BuiltinAndAxiomSimplifier)
timesEvaluatorUnification =
    functionEvaluator
        timesSymbol
        [ functionAxiomUnification_ timesSymbol [zero, varNConfig] zero
        , functionAxiomUnification_
            timesSymbol
            [succ varMConfig, varNConfig]
            (plus varNConfig (times varMConfig varNConfig))
        ]

fibonacciEvaluatorUnification :: (AxiomIdentifier, BuiltinAndAxiomSimplifier)
fibonacciEvaluatorUnification =
    functionEvaluator
        fibonacciSymbol
        [ functionAxiomUnification_ fibonacciSymbol [zero] one
        , functionAxiomUnification_ fibonacciSymbol [one] one
        , functionAxiomUnification_
            fibonacciSymbol
            [succ (succ varNConfig)]
            (plus (fibonacci (succ varNConfig)) (fibonacci varNConfig))
        ]

factorialEvaluatorUnification :: (AxiomIdentifier, BuiltinAndAxiomSimplifier)
factorialEvaluatorUnification =
    functionEvaluator
        factorialSymbol
        [ functionAxiomUnification_
            factorialSymbol
            [zero]
            (succ zero)
        , functionAxiomUnification_
            factorialSymbol
            [succ varNConfig]
            (times (succ varNConfig) (factorial varNConfig))
        ]

natSimplifiersUnification :: BuiltinAndAxiomSimplifierMap
natSimplifiersUnification =
    Map.fromList
        [ plusEvaluatorUnification
        , timesEvaluatorUnification
        , fibonacciEvaluatorUnification
        , factorialEvaluatorUnification
        ]

-- | Add an unsatisfiable requirement to the 'Equation'.
requiresBottom ::
    Equation RewritingVariableName -> Equation RewritingVariableName
requiresBottom equation = equation{requires = makeEqualsPredicate zero one}

{- | Add an unsatisfiable @\\equals@ requirement to the 'Equation'.

In contrast to 'requiresBottom', @requiresFatalEquals@ also includes a
requirement which results in a fatal error when evaluated.
-}
requiresFatalEquals ::
    Equation RewritingVariableName -> Equation RewritingVariableName
requiresFatalEquals equation =
    equation
        { requires =
            makeAndPredicate
                (makeEqualsPredicate (fatal zero) one)
                (makeEqualsPredicate zero one)
        }

{- | Add an unsatisfiable @\\in@ requirement to the 'Equation'.

In contrast to 'requiresBottom', @requiresFatalEquals@ also includes a
requirement which results in a fatal error when evaluated.
-}
requiresFatalIn ::
    Equation RewritingVariableName -> Equation RewritingVariableName
requiresFatalIn equation =
    equation
        { requires =
            makeAndPredicate
                (makeEqualsPredicate (fatal zero) one)
                (makeCeilPredicate (mkAnd zero one))
        }

{- | Test short-circuiting evaluation of function requirements.

We want to check that functions are not evaluated in an 'Equation'
requirement if the pre-condition is known to be unsatisfiable without function
evaluation. We check this by including a 'requires' clause with one
unsatisfiable condition and one "fatal" condition (a condition producing a fatal
error if evaluated). If we do function evaluation on the unsatisfiable
requirement, a fatal error will be produced.
-}
test_short_circuit :: [TestTree]
test_short_circuit =
    [ notApplies
        "requires 0 = 1 does not apply"
        [requiresBottom plusZeroRule]
        (plus zero one)
    , notApplies
        "requires fatal(0) = 1 ∧ 0 = 1 does not apply"
        [requiresFatalEquals plusZeroRule]
        (plus zero one)
    , notApplies
        "requires fatal(0) = 1 ∧ 0 ∈ 1 does not apply"
        [requiresFatalIn plusZeroRule]
        (plus zero one)
    ]

{- | A symbol which throws a fatal error when evaluated.

@fatalSymbol@ is useful for checking that symbols in certain positions are never
evaluated.
-}
fatalSymbol :: Symbol
fatalSymbol = Mock.symbol "fatal" [natSort] natSort & function

fatal :: TermLike RewritingVariableName -> TermLike RewritingVariableName
fatal x = mkApplySymbol fatalSymbol [x]

fatalEvaluator :: (AxiomIdentifier, BuiltinAndAxiomSimplifier)
fatalEvaluator =
    ( AxiomIdentifier.Application ident
    , BuiltinAndAxiomSimplifier $ \_ _ -> error "fatal error"
    )
  where
    ident = symbolConstructor fatalSymbol

fatalSimplifiers :: BuiltinAndAxiomSimplifierMap
fatalSimplifiers = uncurry Map.singleton fatalEvaluator

test_List :: [TestTree]
test_List =
    [ applies
        "lengthList([]) => ... ~ lengthList([])"
        [lengthListUnitRule]
        (lengthList unitList)
    , notApplies
        "lengthList([]) => ... ~ lengthList(L)"
        [lengthListUnitRule]
        (lengthList varLConfig)
    , notApplies
        "lengthList([]) => ... !~ lengthList([1])"
        [lengthListUnitRule]
        (lengthList (mkList [mkInt 1]))
    , notApplies
        "lengthList([]) => ... !~ lengthList([1, 2])"
        [lengthListUnitRule]
        (lengthList (mkList [mkInt 1, mkInt 2]))
    , notApplies
        "lengthList(x : xs) => ... !~ lengthList([])"
        [lengthListConsRule]
        (lengthList unitList)
    , notApplies
        "lengthList(x : xs) => ... !~ lengthList(L)"
        [lengthListConsRule]
        (lengthList varLConfig)
    , applies
        "lengthList(x : xs) => ... ~ lengthList([1])"
        [lengthListConsRule]
        (lengthList (mkList [mkInt 1]))
    , applies
        "lengthList(x : xs) => ... ~ lengthList([1, 2])"
        [lengthListConsRule]
        (lengthList (mkList [mkInt 1, mkInt 2]))
    , applies
        "lengthList([]) => ..."
        lengthListRules
        (lengthList unitList)
    , applies
        "lengthList([1]) => ..."
        lengthListRules
        (lengthList (mkList [mkInt 1]))
    , applies
        "lengthList([12]) => ..."
        lengthListRules
        (lengthList (mkList [mkInt 1, mkInt 2]))
    , equals
        "lengthList([]) = 0 : Int"
        (lengthList (mkList []))
        [mkInt 0]
    , equals
        "lengthList([1]) = 1 : Int"
        (lengthList (mkList [mkInt 1]))
        [mkInt 1]
    , equals
        "lengthList([1, 2]) = 2 : Int"
        (lengthList (mkList [mkInt 1, mkInt 2]))
        [mkInt 2]
    , applies
        "removeList([], M) => ... ~ removeList([], [(0, 1)])"
        [removeListUnitRule]
        (removeList unitList (mkMap [(mkInt 0, mkInt 1)] []))
    , equals
        "removeList([1], [(0, 1)]) = [(0, 1)]"
        (removeList (mkList [mkInt 1]) (mkMap [(mkInt 0, mkInt 1)] []))
        [mkMap [(mkInt 0, mkInt 1)] []]
    ]

listSort, intSort, mapSort :: Sort
listSort = Builtin.listSort
intSort = Builtin.intSort
mapSort = Builtin.mapSort

mkList :: [TermLike RewritingVariableName] -> TermLike RewritingVariableName
mkList = List.asInternal

mkInt :: Integer -> TermLike RewritingVariableName
mkInt = Int.asInternal

mkMap ::
    [(TermLike RewritingVariableName, TermLike RewritingVariableName)] ->
    [TermLike RewritingVariableName] ->
    TermLike RewritingVariableName
mkMap elements opaques =
    Ac.asInternal Builtin.testMetadataTools Builtin.mapSort $
        Map.normalizedMap elements opaques

removeMap ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName
removeMap = Builtin.removeMap

addInt ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName
addInt = Builtin.addInt

unitList :: TermLike RewritingVariableName
unitList = mkList []

varXConfig, varYConfig, varLConfig, mMapConfigTerm :: TermLike RewritingVariableName
varXConfig = mkElemVar xConfigInt
varYConfig = mkElemVar yConfigInt
varLConfig = mkElemVar (configElementVariableFromId (testId "lList") listSort)
mMapConfigTerm = mkElemVar mMapConfig

mMapConfig :: ElementVariable RewritingVariableName
mMapConfig = configElementVariableFromId (testId "mMap") mapSort

lengthListSymbol :: Symbol
lengthListSymbol = Mock.symbol "lengthList" [listSort] intSort & function

lengthList :: TermLike RewritingVariableName -> TermLike RewritingVariableName
lengthList l = mkApplySymbol lengthListSymbol [l]

concatList ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName
concatList = Builtin.concatList

consList ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName
consList x xs = concatList (mkList [x]) xs

lengthListUnitRule, lengthListConsRule :: Equation RewritingVariableName
lengthListUnitRule = axiom_ (lengthList unitList) (mkInt 0)
lengthListConsRule =
    axiom_
        (lengthList (consList varXConfig varLConfig))
        (addInt (mkInt 1) (lengthList varLConfig))

lengthListRules :: [Equation RewritingVariableName]
lengthListRules = [lengthListUnitRule, lengthListConsRule]

lengthListEvaluator :: (AxiomIdentifier, BuiltinAndAxiomSimplifier)
lengthListEvaluator = functionEvaluator lengthListSymbol lengthListRules

removeListSymbol :: Symbol
removeListSymbol =
    Mock.symbol "removeList" [listSort, mapSort] mapSort & function

removeList ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName
removeList l m = mkApplySymbol removeListSymbol [l, m]

removeListUnitRule, removeListConsRule :: Equation RewritingVariableName
removeListUnitRule = axiom_ (removeList unitList mMapConfigTerm) mMapConfigTerm
removeListConsRule =
    axiom_
        (removeList (consList varXConfig varLConfig) mMapConfigTerm)
        (removeMap mMapConfigTerm varXConfig)

removeListRules :: [Equation RewritingVariableName]
removeListRules = [removeListUnitRule, removeListConsRule]

removeListEvaluator :: (AxiomIdentifier, BuiltinAndAxiomSimplifier)
removeListEvaluator = functionEvaluator removeListSymbol removeListRules

listSimplifiers :: BuiltinAndAxiomSimplifierMap
listSimplifiers =
    Map.fromList
        [ lengthListEvaluator
        , removeListEvaluator
        , (addIntId, builtinEvaluation addIntEvaluator)
        , (removeMapId, builtinEvaluation removeMapEvaluator)
        ]
  where
    Just addIntEvaluator = Map.lookup "INT.add" Int.builtinFunctions
    addIntId =
        AxiomIdentifier.Application $
            symbolConstructor Builtin.addIntSymbol
    Just removeMapEvaluator = Map.lookup "MAP.remove" Map.builtinFunctions
    removeMapId =
        AxiomIdentifier.Application $
            symbolConstructor Builtin.removeMapSymbol

test_updateList :: [TestTree]
test_updateList =
    [ notApplies
        "different concrete indices"
        [updateListSimplifier]
        ( updateList
            (updateList singletonList (mkInt 0) (mkInt 1))
            (mkInt 1)
            (mkInt 2)
        )
    , applies
        "same concrete indices"
        [updateListSimplifier]
        ( updateList
            (updateList singletonList (mkInt 0) (mkInt 1))
            (mkInt 0)
            (mkInt 2)
        )
    , notApplies
        "different abstract keys; evaluates requires with SMT"
        [updateListSimplifier]
        ( updateList
            (updateList varLConfig (mkElemVar xConfigInt) (mkInt 1))
            (addInt (mkElemVar xConfigInt) (mkInt 1))
            (mkInt 2)
        )
    , notApplies
        "different keys; evaluates requires with function rule"
        [updateListSimplifier]
        ( updateList
            (updateList Builtin.unitList (mkInt 0) (mkInt 1))
            (addInt (mkInt 0) (Builtin.dummyInt (mkInt 1)))
            (mkInt 2)
        )
    , equals
        "different keys; evaluates updateList"
        ( updateList
            (updateList twoElementList (mkInt 0) (mkInt 1))
            (addInt (mkInt 0) (Builtin.dummyInt (mkInt 1)))
            (mkInt 2)
        )
        [mkList [mkInt 1, mkInt 2]]
    , equals
        "negative index"
        (updateList singletonList (mkInt (-1)) (mkInt 1))
        [mkBottom_]
    , equals
        "positive index outside rage"
        (updateList singletonList (mkInt 1) (mkInt 1))
        [mkBottom_]
    , applies
        "same abstract key"
        [updateListSimplifier]
        ( updateList
            (updateList singletonList (mkElemVar xConfigInt) (mkInt 1))
            (mkElemVar xConfigInt)
            (mkInt 2)
        )
    ]

singletonList :: TermLike RewritingVariableName
singletonList = Builtin.elementList (mkInt 0)

twoElementList :: TermLike RewritingVariableName
twoElementList = Builtin.concatList singletonList singletonList

updateList ::
    -- | List
    TermLike RewritingVariableName ->
    -- | Index
    TermLike RewritingVariableName ->
    -- | Value
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName
updateList = Builtin.updateList

updateListSimplifier :: Equation RewritingVariableName
updateListSimplifier =
    axiom
        (updateList (updateList varLConfig u v) x y)
        (updateList varLConfig u y)
        (makeEqualsPredicate (Builtin.keqBool (injK u) (injK x)) (mkBool True))
  where
    [u, v, x, y] = mkElemVar <$> [uConfigInt, vConfigInt, xConfigInt, yConfigInt]
    injK = Builtin.inj Builtin.kSort

test_lookupMap :: [TestTree]
test_lookupMap =
    [ equals
        "lookupMap(.Map, 1) = \\bottom"
        (lookupMap (mkMap [] []) (mkInt 1))
        []
    , equals
        "lookupMap(1 |-> 2, 1) = 2"
        (lookupMap (mkMap [(mkInt 1, mkInt 2)] []) (mkInt 1))
        [mkInt 2]
    , equals
        "lookupMap(0 |-> 1  1 |-> 2, 1) = 2"
        (lookupMap (mkMap [(mkInt 0, mkInt 1), (mkInt 1, mkInt 2)] []) (mkInt 1))
        [mkInt 2]
    ]

lookupMapSymbol :: Symbol
lookupMapSymbol = Builtin.lookupMapSymbol

lookupMap ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName
lookupMap = Builtin.lookupMap

lookupMapRule :: Equation RewritingVariableName
lookupMapRule =
    axiom_
        ( lookupMap
            (mkMap [(varXConfig, varYConfig)] [mMapConfigTerm])
            varXConfig
        )
        varYConfig

lookupMapRules :: [Equation RewritingVariableName]
lookupMapRules = [lookupMapRule]

lookupMapEvaluator :: (AxiomIdentifier, BuiltinAndAxiomSimplifier)
lookupMapEvaluator = functionEvaluator lookupMapSymbol lookupMapRules

test_updateMap :: [TestTree]
test_updateMap =
    [ notApplies
        "different concrete keys"
        [updateMapSimplifier]
        ( updateMap
            (updateMap mMapConfigTerm (mkInt 0) (mkInt 1))
            (mkInt 1)
            (mkInt 2)
        )
    , applies
        "same concrete key"
        [updateMapSimplifier]
        ( updateMap
            (updateMap mMapConfigTerm (mkInt 0) (mkInt 1))
            (mkInt 0)
            (mkInt 2)
        )
    , notApplies
        "different abstract keys; evaluates requires with SMT"
        [updateMapSimplifier]
        ( updateMap
            (updateMap mMapConfigTerm (mkElemVar xConfigInt) (mkInt 1))
            (addInt (mkElemVar xConfigInt) (mkInt 1))
            (mkInt 2)
        )
    , notApplies
        "different keys; evaluates requires with function rule"
        [updateMapSimplifier]
        ( updateMap
            (updateMap Builtin.unitMap (mkInt 0) (mkInt 1))
            (addInt (mkInt 0) (Builtin.dummyInt (mkInt 1)))
            (mkInt 2)
        )
    , equals
        "different keys; evaluates updateMap"
        ( updateMap
            (updateMap Builtin.unitMap (mkInt 0) (mkInt 1))
            (addInt (mkInt 0) (Builtin.dummyInt (mkInt 1)))
            (mkInt 2)
        )
        [mkMap [(mkInt 0, mkInt 1), (mkInt 1, mkInt 2)] []]
    , applies
        "same abstract key"
        [updateMapSimplifier]
        ( updateMap
            (updateMap mMapConfigTerm (mkElemVar xConfigInt) (mkInt 1))
            (mkElemVar xConfigInt)
            (mkInt 2)
        )
    ]

updateMap ::
    -- | Map
    TermLike RewritingVariableName ->
    -- | Key
    TermLike RewritingVariableName ->
    -- | Value
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName
updateMap = Builtin.updateMap

updateMapSimplifier :: Equation RewritingVariableName
updateMapSimplifier =
    axiom
        (updateMap (updateMap mMapConfigTerm u v) x y)
        (updateMap mMapConfigTerm u y)
        (makeEqualsPredicate (Builtin.keqBool (injK u) (injK x)) (mkBool True))
  where
    [u, v, x, y] = mkElemVar <$> [uConfigInt, vConfigInt, xConfigInt, yConfigInt]
    injK = Builtin.inj Builtin.kSort

dummyIntSimplifier :: Equation RewritingVariableName
dummyIntSimplifier =
    axiom_ (Builtin.dummyInt (mkElemVar xConfigInt)) (mkElemVar xConfigInt)

mkBool :: Bool -> TermLike RewritingVariableName
mkBool = Bool.asInternal

mapSimplifiers :: BuiltinAndAxiomSimplifierMap
mapSimplifiers =
    Map.fromList
        [ lookupMapEvaluator
        , functionSimplifier Builtin.updateMapSymbol [updateMapSimplifier]
        , functionEvaluator
            Builtin.dummyIntSymbol
            [dummyIntSimplifier]
        ]

uConfigInt, vConfigInt, xConfigInt, yConfigInt :: ElementVariable RewritingVariableName
uConfigInt = configElementVariableFromId (testId "uInt") intSort
vConfigInt = configElementVariableFromId (testId "vInt") intSort
xConfigInt = configElementVariableFromId (testId "xInt") intSort
yConfigInt = configElementVariableFromId (testId "yInt") intSort

xsConfigInt :: SetVariable RewritingVariableName
xsConfigInt =
    mkSetVariable (testId "xsInt") intSort
        & mapSetVariable (pure mkConfigVariable)

test_Ceil :: [TestTree]
test_Ceil =
    [ simplifies
        "\\ceil(dummy(X)) => ... ~ \\ceil(dummy(Y))"
        ceilDummyRule
        (mkCeil_ $ Builtin.dummyInt $ mkElemVar yConfigInt)
    , notSimplifies
        "\\ceil(dummy(X)) => \\not(\\equals(X, 0)) !~ dummy(Y)"
        ceilDummyRule
        (Builtin.dummyInt $ mkElemVar yConfigInt)
    , simplifies
        "\\ceil(dummy(@X)) => ... ~ \\ceil(dummy(Y))"
        ceilDummySetRule
        (mkCeil_ $ Builtin.dummyInt $ mkElemVar yConfigInt)
    ]

ceilDummyRule :: Equation RewritingVariableName
ceilDummyRule =
    axiom_
        (mkCeil_ $ Builtin.dummyInt $ mkElemVar xConfigInt)
        (mkEquals_ (Builtin.eqInt (mkElemVar xConfigInt) (mkInt 0)) (mkBool False))

ceilDummySetRule :: Equation RewritingVariableName
ceilDummySetRule =
    axiom_
        (mkCeil_ $ Builtin.dummyInt $ mkSetVar xsConfigInt)
        (mkEquals_ (Builtin.eqInt (mkSetVar xsConfigInt) (mkInt 0)) (mkBool False))

-- Simplification tests: check that one or more rules applies or not
withSimplified ::
    (CommonAttemptedAxiom -> Assertion) ->
    TestName ->
    Equation RewritingVariableName ->
    TermLike RewritingVariableName ->
    TestTree
withSimplified check comment rule term =
    testCase comment $ do
        actual <- evaluateWith (simplificationEvaluation rule) term
        check actual

simplifies
    , notSimplifies ::
        TestName ->
        Equation RewritingVariableName ->
        TermLike RewritingVariableName ->
        TestTree
simplifies =
    withSimplified $ \attempted -> do
        results <- expectApplied attempted
        expectNoRemainders results
  where
    expectApplied NotApplicable = assertFailure "Expected Applied"
    expectApplied (NotApplicableUntilConditionChanges _) =
        assertFailure "Expected Applied"
    expectApplied (Applied results) = return results
    expectNoRemainders =
        assertBool "Expected no remainders"
            . isBottom
            . Lens.view (field @"remainders")
notSimplifies =
    withSimplified (assertBool "Expected NotApplicable" . isNotApplicable)

axiomEvaluator ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    BuiltinAndAxiomSimplifier
axiomEvaluator left right =
    simplificationEvaluation (axiom left right makeTruePredicate)

axiomEvaluatorUnification ::
    Symbol ->
    [TermLike RewritingVariableName] ->
    TermLike RewritingVariableName ->
    BuiltinAndAxiomSimplifier
axiomEvaluatorUnification symbol args right =
    simplificationEvaluation
        (functionAxiomUnification symbol args right makeTruePredicate)

appliedMockEvaluator ::
    Pattern VariableName -> BuiltinAndAxiomSimplifier
appliedMockEvaluator result =
    BuiltinAndAxiomSimplifier $
        mockEvaluator $
            AttemptedAxiom.Applied
                AttemptedAxiomResults
                    { results =
                        OrPattern.fromPatterns
                            [Test.Kore.Rewrite.Function.Integration.mapVariablesConfig result]
                    , remainders = OrPattern.fromPatterns []
                    }

mapVariablesConfig ::
    Pattern VariableName ->
    Pattern RewritingVariableName
mapVariablesConfig =
    Pattern.mapVariables (pure worker)
  where
    worker :: VariableName -> RewritingVariableName
    worker v = mkConfigVariable v{counter = Just (Element 1)}

mockEvaluator ::
    Monad simplifier =>
    AttemptedAxiom variable ->
    TermLike variable ->
    SideCondition variable ->
    simplifier (AttemptedAxiom variable)
mockEvaluator evaluation _ _ = return evaluation
-- ---------------------------------------------------------------------

-- * Definition

natModuleName :: ModuleName
natModuleName = ModuleName "NAT"

natSortDecl :: Sentence pattern'
natSortDecl =
    asSentence
        SentenceSort
            { sentenceSortName =
                let SortActualSort SortActual{sortActualName} = natSort
                 in sortActualName
            , sentenceSortParameters = []
            , sentenceSortAttributes = Attributes []
            }

-- | Declare the @BOOL@ builtins.
natModule :: ParsedModule
natModule =
    Module
        { moduleName = natModuleName
        , moduleAttributes = Attributes []
        , moduleSentences =
            [ natSortDecl
            , Builtin.symbolDecl zeroSymbol
            , Builtin.symbolDecl succSymbol
            , Builtin.symbolDecl plusSymbol
            , Builtin.symbolDecl timesSymbol
            , Builtin.symbolDecl fibonacciSymbol
            , Builtin.symbolDecl factorialSymbol
            ]
        }

testModuleName :: ModuleName
testModuleName = ModuleName "INTEGRATION-TEST"

testModule :: ParsedModule
testModule =
    Module
        { moduleName = testModuleName
        , moduleAttributes = Attributes []
        , moduleSentences =
            [ Builtin.importParsedModule Builtin.testModuleName
            , Builtin.importParsedModule natModuleName
            , Builtin.subsortDecl Builtin.intSort Builtin.kSort
            ]
        }

testDefinition :: ParsedDefinition
testDefinition =
    Builtin.testDefinition
        & field @"definitionModules" Lens.<>~ [natModule, testModule]

verify ::
    ParsedDefinition ->
    Either
        (Kore.Error.Error VerifyError)
        ( Map ModuleName (VerifiedModule Attribute.Symbol)
        )
verify = verifyAndIndexDefinition Builtin.koreVerifiers

verifiedModules ::
    Map ModuleName (VerifiedModule Attribute.Symbol)
verifiedModules = Kore.Error.assertRight (verify testDefinition)

verifiedModule :: VerifiedModule Attribute.Symbol
Just verifiedModule = Map.lookup testModuleName verifiedModules

testMetadataTools :: SmtMetadataTools Attribute.Symbol
testMetadataTools = MetadataTools.build verifiedModule

testConditionSimplifier ::
    MonadSimplify simplifier => ConditionSimplifier simplifier
testConditionSimplifier =
    Simplifier.Condition.create SubstitutionSimplifier.substitutionSimplifier

testEvaluators :: BuiltinAndAxiomSimplifierMap
testEvaluators = Builtin.koreEvaluators verifiedModule

testInjSimplifier :: InjSimplifier
testInjSimplifier =
    mkInjSimplifier $ SortGraph.fromIndexedModule verifiedModule

testEnv :: MonadSimplify simplifier => Env simplifier
testEnv =
    Env
        { metadataTools = testMetadataTools
        , simplifierCondition = testConditionSimplifier
        , simplifierAxioms =
            mconcat
                [ testEvaluators
                , natSimplifiers
                , listSimplifiers
                , mapSimplifiers
                , fatalSimplifiers
                ]
        , memo = Memo.forgetful
        , injSimplifier = testInjSimplifier
        , overloadSimplifier = Mock.overloadSimplifier
        }

testEnvUnification :: Env (SimplifierT NoSMT)
testEnvUnification =
    testEnv
        { simplifierAxioms =
            mconcat
                [ testEvaluators
                , natSimplifiersUnification
                , listSimplifiers
                , mapSimplifiers
                , fatalSimplifiers
                ]
        }
