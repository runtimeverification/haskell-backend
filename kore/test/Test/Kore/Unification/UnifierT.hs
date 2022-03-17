module Test.Kore.Unification.UnifierT (
    test_mergeAndNormalizeSubstitutions,
    test_simplifyCondition,
) where

import Data.Map.Strict qualified as Map
import Kore.Equation qualified as Equation
import Kore.Internal.Condition (
    Condition,
 )
import Kore.Internal.Condition qualified as Condition
import Kore.Internal.Conditional (
    Conditional (..),
 )
import Kore.Internal.Conditional qualified as Conditional
import Kore.Internal.MultiOr (
    MultiOr,
 )
import Kore.Internal.MultiOr qualified as MultiOr
import Kore.Internal.OrCondition qualified as OrCondition
import Kore.Internal.Predicate qualified as Predicate
import Kore.Internal.SideCondition qualified as SideCondition (
    top,
 )
import Kore.Internal.Substitution (
    Assignment,
 )
import Kore.Internal.Substitution qualified as Substitution
import Kore.Internal.TermLike
import Kore.Rewrite.Axiom.EvaluationStrategy qualified as EvaluationStrategy
import Kore.Rewrite.Axiom.Identifier qualified as Axiom.Identifier
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.Condition qualified as Condition
import Kore.Simplify.Data (
    Env (..),
 )
import Kore.Simplify.Not qualified as Not
import Kore.Simplify.Simplify (SimplifierXSwitch (..))
import Kore.Simplify.Simplify qualified as Simplifier
import Kore.Unification.UnifierT qualified as Monad.Unify
import Logic qualified
import Prelude.Kore
import Test.Kore.Rewrite.MockSymbols qualified as Mock
import Test.Kore.Simplify qualified as Test
import Test.Tasty
import Test.Tasty.HUnit.Ext

assertNormalized :: Condition RewritingVariableName -> IO ()
assertNormalized expect = do
    actual <- normalizeExcept expect
    assertEqual
        "Expected original result"
        (MultiOr.make [expect])
        actual
    assertNormalizedPredicatesMulti actual

test_simplifyCondition :: [TestTree]
test_simplifyCondition =
    [ testCase "predicate = \\bottom" $ do
        let expect = mempty
        actual <- normalize Condition.bottomCondition
        assertEqual "Expected empty result" expect actual
        assertNormalizedPredicatesMulti actual
    , testCase "∃ y z. x = σ(y, z)" $ do
        let expect = Condition.fromPredicate existsPredicate
        assertNormalized expect
    , testCase "¬∃ y z. x = σ(y, z)" $ do
        let expect =
                Condition.fromPredicate $
                    Predicate.makeNotPredicate existsPredicate
        assertNormalized expect
    , testCase "x = f(x)" $ do
        let x = inject Mock.xConfig
            expect =
                Predicate.makeEqualsPredicate (mkVar x) (Mock.f (mkVar x))
                    & OrCondition.fromPredicate
            denormalized =
                Substitution.mkUnwrappedSubstitution
                    [(x, Mock.f (mkVar x))]
            input =
                (Condition.fromSubstitution . Substitution.wrap) denormalized
        actual <- normalizeExcept input
        actualSimplifierXEnabled <- normalizeExceptSimplifierXEnabled input
        assertEqual "Expected SubstitutionError" expect actual
        assertEqual "Expected SubstitutionError" expect actualSimplifierXEnabled
    , testCase "x = id(x)" $ do
        let x = inject Mock.xConfig
            expect = OrCondition.fromCondition Condition.top
            input =
                ( Condition.fromSubstitution
                    . Substitution.wrap
                    . Substitution.mkUnwrappedSubstitution
                )
                    [(x, Mock.functional10 (mkVar x))]
        actual <- normalizeExcept input
        assertEqual "Expected \\top" expect actual
    ]
  where
    existsPredicate =
        Predicate.makeMultipleExists [Mock.yConfig, Mock.zConfig] $
            Predicate.makeEqualsPredicate
                (mkElemVar Mock.xConfig)
                (Mock.sigma (mkElemVar Mock.yConfig) (mkElemVar Mock.zConfig))

test_mergeAndNormalizeSubstitutions :: [TestTree]
test_mergeAndNormalizeSubstitutions =
    [ testCase "Constructor normalization"
      -- [x=constructor(a)] + [x=constructor(a)]  === [x=constructor(a)]
      $
        do
            let expect =
                    [ Condition.fromSubstitution $
                        Substitution.unsafeWrap
                            [(inject Mock.xConfig, Mock.constr10 Mock.a)]
                    ]
            actual <-
                merge
                    [
                        ( inject Mock.xConfig
                        , Mock.constr10 Mock.a
                        )
                    ]
                    [
                        ( inject Mock.xConfig
                        , Mock.constr10 Mock.a
                        )
                    ]
            assertEqual "" expect actual
            assertNormalizedPredicatesMulti actual
    , testCase "Constructor normalization with variables"
      -- [x=constructor(y)] + [x=constructor(y)]  === [x=constructor(y)]
      $
        do
            let expect =
                    [ Condition.fromSubstitution $
                        Substitution.unsafeWrap
                            [
                                ( inject Mock.xConfig
                                , Mock.constr10 (mkElemVar Mock.yConfig)
                                )
                            ]
                    ]
            actual <-
                merge
                    [
                        ( inject Mock.xConfig
                        , Mock.constr10 (mkElemVar Mock.yConfig)
                        )
                    ]
                    [
                        ( inject Mock.xConfig
                        , Mock.constr10 (mkElemVar Mock.yConfig)
                        )
                    ]
            assertEqual "" expect actual
            assertNormalizedPredicatesMulti actual
    , testCase "Double constructor is bottom"
      -- [x=constructor(a)] + [x=constructor(constructor(a))]  === bottom?
      $
        do
            let expect = []
            actual <-
                merge
                    [
                        ( inject Mock.xConfig
                        , Mock.constr10 Mock.a
                        )
                    ]
                    [
                        ( inject Mock.xConfig
                        , Mock.constr10 (Mock.constr10 Mock.a)
                        )
                    ]
            assertEqual "" expect actual
            assertNormalizedPredicatesMulti actual
    , testCase "Double constructor is bottom with variables"
      -- [x=constructor(y)] + [x=constructor(constructor(y))]  === bottom?
      $
        do
            let expect =
                    [ Substitution.assign
                        (inject Mock.xConfig)
                        ( Mock.constr10
                            ( mkAnd
                                (Mock.constr10 (mkElemVar Mock.yConfig))
                                (mkElemVar Mock.yConfig)
                            )
                        )
                    ]
                        & Substitution.wrap
                        & Conditional.fromSubstitution
            actual <-
                merge
                    [
                        ( inject Mock.xConfig
                        , Mock.constr10 (mkElemVar Mock.yConfig)
                        )
                    ]
                    [
                        ( inject Mock.xConfig
                        , Mock.constr10 (Mock.constr10 (mkElemVar Mock.yConfig))
                        )
                    ]
            assertEqual "" [expect] actual
            assertNormalizedPredicatesMulti actual
    , testCase "Constructor and constructor of function"
      -- [x=constructor(a)] + [x=constructor(f(a))]
      $
        do
            let expect =
                    [ Conditional
                        { term = ()
                        , predicate =
                            Predicate.makeEqualsPredicate
                                Mock.a
                                (Mock.f Mock.a)
                        , substitution =
                            Substitution.unsafeWrap
                                [
                                    ( inject Mock.xConfig
                                    , Mock.constr10 Mock.a
                                    )
                                ]
                        }
                    ]
            actual <-
                merge
                    [
                        ( inject Mock.xConfig
                        , Mock.constr10 Mock.a
                        )
                    ]
                    [
                        ( inject Mock.xConfig
                        , Mock.constr10 (Mock.f Mock.a)
                        )
                    ]
            assertEqual "" expect actual
            assertNormalizedPredicatesMulti actual
    , testCase "Constructor and constructor of function with variables" $ do
        let ctor = Mock.constr10
            f = Mock.f
            y = mkElemVar Mock.yConfig
        let denormCondition =
                Predicate.makeEqualsPredicate y (f y)
                    & Condition.fromPredicate
            substCondition =
                Substitution.assign (inject Mock.xConfig) (ctor (f y))
                    & Condition.fromSingleSubstitution
        let expect =
                denormCondition <> substCondition
                    & pure
        actual <-
            merge
                [(inject Mock.xConfig, ctor y)]
                [(inject Mock.xConfig, ctor (f y))]
        assertEqual "" expect actual
        assertNormalizedPredicatesMulti actual
    , testCase "Constructor circular dependency?"
      -- [x=y] + [y=constructor(x)]  === error
      $
        do
            let expect =
                    [ Predicate.makeEqualsPredicate
                        (mkElemVar Mock.xConfig)
                        ( mkAnd
                            (Mock.constr10 (mkElemVar Mock.xConfig))
                            (mkElemVar Mock.yConfig)
                        )
                        & Condition.fromPredicate
                    ]
            actual <-
                merge
                    [
                        ( inject Mock.xConfig
                        , mkElemVar Mock.yConfig
                        )
                    ]
                    [
                        ( inject Mock.xConfig
                        , Mock.constr10 (mkElemVar Mock.xConfig)
                        )
                    ]
            assertEqual "" expect actual
            assertNormalizedPredicatesMulti actual
    , testCase "Non-ctor circular dependency" $ do
        let denormCondition =
                Predicate.makeEqualsPredicate
                    (mkElemVar Mock.yConfig)
                    (Mock.f (mkElemVar Mock.yConfig))
                    & Condition.fromPredicate
            substCondition =
                Substitution.assign (inject Mock.xConfig) (mkElemVar Mock.yConfig)
                    & Condition.fromSingleSubstitution
        let expect =
                denormCondition <> substCondition
                    & pure
        actual <-
            merge
                [
                    ( inject Mock.xConfig
                    , mkElemVar Mock.yConfig
                    )
                ]
                [
                    ( inject Mock.yConfig
                    , Mock.f (mkElemVar Mock.xConfig)
                    )
                ]
        actualSimplifierXEnabled <-
            mergeSimplifierXEnabled
                [
                    ( inject Mock.xConfig
                    , mkElemVar Mock.yConfig
                    )
                ]
                [
                    ( inject Mock.yConfig
                    , Mock.f (mkElemVar Mock.xConfig)
                    )
                ]

        assertEqual "" expect actual
        assertEqual "" expect actualSimplifierXEnabled
        assertNormalizedPredicatesMulti actual
    , testCase "Normalizes substitution" $
        do
            let expect =
                    [ Condition.fromSubstitution $
                        Substitution.unsafeWrap
                            [ (inject Mock.xConfig, Mock.constr10 Mock.a)
                            , (inject Mock.yConfig, Mock.a)
                            ]
                    ]
            actual <-
                normalize $
                    Condition.fromSubstitution $
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [ (inject Mock.xConfig, Mock.constr10 Mock.a)
                                ,
                                    ( inject Mock.xConfig
                                    , Mock.constr10 (mkElemVar Mock.yConfig)
                                    )
                                ]
            assertEqual "" expect actual
            assertNormalizedPredicatesMulti actual
    , testCase "Predicate from normalizing substitution" $
        do
            let expect =
                    [ Conditional
                        { term = ()
                        , predicate =
                            Predicate.makeEqualsPredicate Mock.cf Mock.cg
                        , substitution =
                            Substitution.unsafeWrap
                                [(inject Mock.xConfig, Mock.constr10 Mock.cf)]
                        }
                    ]
            actual <-
                normalize
                    Conditional
                        { term = ()
                        , predicate = Predicate.makeTruePredicate
                        , substitution =
                            Substitution.wrap $
                                Substitution.mkUnwrappedSubstitution
                                    [ (inject Mock.xConfig, Mock.constr10 Mock.cf)
                                    , (inject Mock.xConfig, Mock.constr10 Mock.cg)
                                    ]
                        }
            assertEqual "" expect actual
            assertNormalizedPredicatesMulti actual
    , testCase "Normalizes substitution and substitutes in predicate" $
        do
            let expect =
                    [ Conditional
                        { term = ()
                        , predicate =
                            Predicate.makeCeilPredicate $
                                Mock.f Mock.a
                        , substitution =
                            Substitution.unsafeWrap
                                [ (inject Mock.xConfig, Mock.constr10 Mock.a)
                                , (inject Mock.yConfig, Mock.a)
                                ]
                        }
                    ]
            actual <-
                normalize
                    Conditional
                        { term = ()
                        , predicate =
                            Predicate.makeCeilPredicate $
                                Mock.f (mkElemVar Mock.yConfig)
                        , substitution =
                            Substitution.wrap $
                                Substitution.mkUnwrappedSubstitution
                                    [ (inject Mock.xConfig, Mock.constr10 Mock.a)
                                    ,
                                        ( inject Mock.xConfig
                                        , Mock.constr10 (mkElemVar Mock.yConfig)
                                        )
                                    ]
                        }
            assertEqual "" expect actual
            assertNormalizedPredicatesMulti actual
    ]
merge
    , mergeSimplifierXEnabled ::
        [(SomeVariable RewritingVariableName, TermLike RewritingVariableName)] ->
        [(SomeVariable RewritingVariableName, TermLike RewritingVariableName)] ->
        IO [Condition RewritingVariableName]
merge = mergeSimplifierX DisabledSimplifierX
mergeSimplifierXEnabled = mergeSimplifierX EnabledSimplifierX

mergeSimplifierX ::
    SimplifierXSwitch ->
    [(SomeVariable RewritingVariableName, TermLike RewritingVariableName)] ->
    [(SomeVariable RewritingVariableName, TermLike RewritingVariableName)] ->
    IO [Condition RewritingVariableName]
mergeSimplifierX
    simplifierXSwitch
    (Substitution.mkUnwrappedSubstitution -> s1)
    (Substitution.mkUnwrappedSubstitution -> s2) =
        Test.runSimplifier mockEnv $
            Monad.Unify.runUnifierT Not.notSimplifier $
                mergeSubstitutionsExcept $
                    Substitution.wrap
                        . fmap simplifiedAssignment
                        <$> [s1, s2]
      where
        simplifiedAssignment ::
            Assignment RewritingVariableName ->
            Assignment RewritingVariableName
        simplifiedAssignment =
            Substitution.mapAssignedTerm Test.simplifiedTerm

        mergeSubstitutionsExcept =
            Logic.lowerLogicT
                . Simplifier.simplifyCondition SideCondition.top
                . Condition.fromSubstitution
                . mconcat
        mockEnv = Mock.env{simplifierXSwitch}

normalize ::
    Conditional RewritingVariableName term ->
    IO [Conditional RewritingVariableName term]
normalize =
    Test.runSimplifierBranch mockEnv
        . Condition.simplifyCondition SideCondition.top
  where
    mockEnv = Mock.env

normalizeExcept
    , normalizeExceptSimplifierXEnabled ::
        Conditional RewritingVariableName () ->
        IO (MultiOr (Conditional RewritingVariableName ()))
normalizeExcept = normalizeExceptSimplifierX DisabledSimplifierX
normalizeExceptSimplifierXEnabled =
    normalizeExceptSimplifierX EnabledSimplifierX
normalizeExceptSimplifierX ::
    SimplifierXSwitch ->
    Conditional RewritingVariableName () ->
    IO (MultiOr (Conditional RewritingVariableName ()))
normalizeExceptSimplifierX simplifierXSwitch predicated =
    fmap MultiOr.make $
        Test.runSimplifier mockEnv $
            Monad.Unify.runUnifierT Not.notSimplifier $
                Logic.lowerLogicT $
                    Simplifier.simplifyCondition SideCondition.top predicated
  where
    mockEnv = Mock.env{simplifierAxioms, simplifierXSwitch}
    simplifierAxioms =
        -- Use Mock.functional10 as the identity function.
        Map.fromList
            [
                ( Axiom.Identifier.Application Mock.functional10Id
                , EvaluationStrategy.definitionEvaluation
                    [ Equation.mkEquation
                        (Mock.functional10 (mkElemVar Mock.xConfig))
                        (mkElemVar Mock.xConfig)
                    ]
                )
            ]

-- | Check that 'Condition.substitution' is normalized for all arguments.
assertNormalizedPredicatesMulti ::
    Foldable f => f (Condition RewritingVariableName) -> Assertion
assertNormalizedPredicatesMulti =
    traverse_ assertNormalizedPredicatesSingle

-- | Check that 'Condition.substitution' is normalized for all arguments.
assertNormalizedPredicatesSingle :: Condition RewritingVariableName -> Assertion
assertNormalizedPredicatesSingle =
    assertBool "Substitution is normalized"
        . Substitution.isNormalized
        . Condition.substitution
