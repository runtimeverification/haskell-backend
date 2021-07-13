module Test.Kore.Simplify.Condition (
    test_simplify_local_functions,
    test_predicateSimplification,
    test_simplifyPredicates,
) where

import qualified Data.Map.Strict as Map
import Kore.Internal.Condition (
    Condition,
    Conditional (..),
 )
import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.Condition as Conditional
import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import qualified Kore.Internal.MultiAnd as MultiAnd
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrCondition (
    OrCondition,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Predicate (
    Predicate,
    makeAndPredicate,
    makeCeilPredicate,
    makeEqualsPredicate,
    makeFalsePredicate,
    makeTruePredicate,
 )
import Kore.Internal.SideCondition (
    SideCondition,
 )
import qualified Kore.Internal.SideCondition as SideCondition (
    top,
 )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
import Kore.Rewrite.Axiom.EvaluationStrategy (
    firstFullEvaluation,
 )
import qualified Kore.Rewrite.Axiom.Identifier as AxiomIdentifier (
    AxiomIdentifier (..),
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import qualified Kore.Simplify.Condition as Condition
import Kore.Simplify.Simplify
import qualified Kore.Simplify.SubstitutionSimplifier as SubstitutionSimplifier
import Kore.TopBottom
import Prelude.Kore
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import qualified Test.Kore.Simplify as Test
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_simplify_local_functions :: [TestTree]
test_simplify_local_functions =
    [ -- Constructor at top
      test "contradiction: f(x) = a ∧ f(x) = b" f (Right a) (Right b)
    , test "contradiction: a = f(x) ∧ f(x) = b" f (Left a) (Right b)
    , test "contradiction: a = f(x) ∧ b = f(x)" f (Left a) (Left b)
    , test "contradiction: f(x) = a ∧ b = f(x)" f (Right a) (Left b)
    , -- Sort injection at top
      test "contradiction: f(x) = injA ∧ f(x) = injB" f (Right injA) (Right injB)
    , test "contradiction: injA = f(x) ∧ f(x) = injB" f (Left injA) (Right injB)
    , test "contradiction: injA = f(x) ∧ injB = f(x)" f (Left injA) (Left injB)
    , test "contradiction: f(x) = injA ∧ injB = f(x)" f (Right injA) (Left injB)
    , -- Int at top
      test "contradiction: f(x) = 2 ∧ f(x) = 3" fInt (Right int2) (Right int3)
    , test "contradiction: 2 = f(x) ∧ f(x) = 3" fInt (Left int2) (Right int3)
    , test "contradiction: 2 = f(x) ∧ 3 = f(x)" fInt (Left int2) (Left int3)
    , test "contradiction: f(x) = 2 ∧ 3 = f(x)" fInt (Right int2) (Left int3)
    , -- Bool at top
      test "contradiction: f(x) = true ∧ f(x) = false" fBool (Right boolTrue) (Right boolFalse)
    , test "contradiction: true = f(x) ∧ f(x) = false" fBool (Left boolTrue) (Right boolFalse)
    , test "contradiction: true = f(x) ∧ false = f(x)" fBool (Left boolTrue) (Left boolFalse)
    , test "contradiction: f(x) = true ∧ false = f(x)" fBool (Right boolTrue) (Left boolFalse)
    , -- String at top
      test "contradiction: f(x) = \"one\" ∧ f(x) = \"two\"" fString (Right strOne) (Right strTwo)
    , test "contradiction: \"one\" = f(x) ∧ f(x) = \"two\"" fString (Left strOne) (Right strTwo)
    , test "contradiction: \"one\" = f(x) ∧ \"two\" = f(x)" fString (Left strOne) (Left strTwo)
    , test "contradiction: f(x) = \"one\" ∧ \"two\" = f(x)" fString (Right strOne) (Left strTwo)
    ]
  where
    f = Mock.f (mkElemVar Mock.xConfig)
    fInt = Mock.fInt (mkElemVar Mock.xConfigInt)
    fBool = Mock.fBool (mkElemVar Mock.xConfigBool)
    fString = Mock.fString (mkElemVar Mock.xConfigString)
    defined = makeCeilPredicate f & Condition.fromPredicate

    a = Mock.a
    b = Mock.b

    injA = Mock.sortInjection10 Mock.a
    injB = Mock.sortInjection10 Mock.b

    int2 = Mock.builtinInt 2
    int3 = Mock.builtinInt 3

    boolTrue = Mock.builtinBool True
    boolFalse = Mock.builtinBool False

    strOne = Mock.builtinString "one"
    strTwo = Mock.builtinString "two"

    mkLocalDefn func (Left t) = makeEqualsPredicate t func
    mkLocalDefn func (Right t) = makeEqualsPredicate func t

    test name func eitherC1 eitherC2 =
        testCase name $ do
            let equals1 = mkLocalDefn func eitherC1 & Condition.fromPredicate
                equals2 = mkLocalDefn func eitherC2 & Condition.fromPredicate
                condition = defined <> equals1 <> defined <> equals2
            actual <- simplify condition
            assertBool "Expected \\bottom" $ isBottom actual

test_predicateSimplification :: [TestTree]
test_predicateSimplification =
    [ testCase "Identity for top and bottom" $ do
        actualBottom <- runSimplifier Map.empty Conditional.bottomCondition
        assertEqual "" mempty actualBottom
        actualTop <- runSimplifier Map.empty Conditional.topCondition
        assertEqual
            ""
            (MultiOr.singleton Conditional.topCondition)
            actualTop
    , testCase "Applies substitution to predicate" $ do
        let expect =
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate
                            (Mock.f Mock.a)
                            (Mock.g Mock.b)
                    , substitution =
                        Substitution.unsafeWrap
                            [ (inject Mock.xConfig, Mock.a)
                            , (inject Mock.yConfig, Mock.b)
                            ]
                    }
        actual <-
            runSimplifier
                Map.empty
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate
                            (Mock.f (mkElemVar Mock.xConfig))
                            (Mock.g (mkElemVar Mock.yConfig))
                    , substitution =
                        Substitution.unsafeWrap
                            [ (inject Mock.xConfig, Mock.a)
                            , (inject Mock.yConfig, Mock.b)
                            ]
                    }
        assertEqual "" (MultiOr.singleton expect) actual
    , testCase "Simplifies predicate after substitution" $ do
        let expect =
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate
                            Mock.functional00
                            Mock.functional01
                    , substitution =
                        Substitution.unsafeWrap
                            [ (inject Mock.xConfig, Mock.functional00)
                            , (inject Mock.yConfig, Mock.functional01)
                            ]
                    }
        actual <-
            runSimplifier
                Map.empty
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate
                            (Mock.constr10 (mkElemVar Mock.xConfig))
                            (Mock.constr10 (mkElemVar Mock.yConfig))
                    , substitution =
                        Substitution.unsafeWrap
                            [ (inject Mock.xConfig, Mock.functional00)
                            , (inject Mock.yConfig, Mock.functional01)
                            ]
                    }
        assertEqual "" (MultiOr.singleton expect) actual
    , testCase "Simplifies predicate after substitution" $ do
        let expect =
                Conditional
                    { term = ()
                    , predicate = makeEqualsPredicate Mock.a Mock.functional00
                    , substitution =
                        Substitution.unsafeWrap
                            [ (inject Mock.xConfig, Mock.functional00)
                            , (inject Mock.yConfig, Mock.functional01)
                            ]
                    }
        actual <-
            runSimplifier
                ( Map.fromList
                    [
                        ( AxiomIdentifier.Application Mock.fId
                        , simplificationEvaluator
                            [ makeEvaluator
                                [
                                    ( Mock.f Mock.functional00
                                    , Mock.functional00
                                    )
                                , (Mock.f Mock.functional01, Mock.a)
                                ]
                            ]
                        )
                    ]
                )
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate
                            (Mock.f (mkElemVar Mock.xConfig))
                            (Mock.f (mkElemVar Mock.yConfig))
                    , substitution =
                        Substitution.unsafeWrap
                            [ (inject Mock.xConfig, Mock.functional00)
                            , (inject Mock.yConfig, Mock.functional01)
                            ]
                    }
        assertEqual "" (MultiOr.singleton expect) actual
    , testCase "Merges substitution from predicate simplification" $ do
        let expect =
                Conditional
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution =
                        Substitution.unsafeWrap
                            [ (inject Mock.xConfig, Mock.a)
                            , (inject Mock.yConfig, Mock.b)
                            ]
                    }
        actual <-
            runSimplifier
                ( Map.fromList
                    [
                        ( AxiomIdentifier.Application Mock.fId
                        , simplificationEvaluator
                            [ makeEvaluator
                                [(Mock.f Mock.b, Mock.constr10 Mock.a)]
                            ]
                        )
                    ]
                )
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate
                            (Mock.constr10 (mkElemVar Mock.xConfig))
                            (Mock.f (mkElemVar Mock.yConfig))
                    , substitution =
                        Substitution.unsafeWrap
                            [ (inject Mock.yConfig, Mock.b)
                            ]
                    }
        assertEqual "" (MultiOr.singleton expect) actual
    , testCase "Reapplies substitution from predicate simplification" $ do
        let expect =
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate
                            (Mock.f Mock.a)
                            (Mock.g Mock.a)
                    , substitution =
                        Substitution.unsafeWrap
                            [ (inject Mock.xConfig, Mock.a)
                            , (inject Mock.yConfig, Mock.b)
                            ]
                    }
        actual <-
            runSimplifier
                ( Map.fromList
                    [
                        ( AxiomIdentifier.Application Mock.fId
                        , simplificationEvaluator
                            [ makeEvaluator
                                [ (Mock.f Mock.b, Mock.constr10 Mock.a)
                                ]
                            ]
                        )
                    ]
                )
                Conditional
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            ( makeEqualsPredicate
                                (Mock.constr10 (mkElemVar Mock.xConfig))
                                (Mock.f (mkElemVar Mock.yConfig))
                            )
                            ( makeEqualsPredicate
                                (Mock.f (mkElemVar Mock.xConfig))
                                (Mock.g Mock.a)
                            )
                    , substitution =
                        Substitution.unsafeWrap
                            [ (inject Mock.yConfig, Mock.b)
                            ]
                    }
        assertEqual "" (MultiOr.singleton expect) actual
    , testCase "Simplifies after reapplying substitution" $ do
        let expect =
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate
                            (Mock.g Mock.a)
                            (Mock.g Mock.b)
                    , substitution =
                        Substitution.unsafeWrap
                            [ (inject Mock.xConfig, Mock.a)
                            , (inject Mock.yConfig, Mock.b)
                            ]
                    }
        actual <-
            runSimplifier
                ( Map.fromList
                    [
                        ( AxiomIdentifier.Application Mock.fId
                        , simplificationEvaluator
                            [ makeEvaluator
                                [ (Mock.f Mock.b, Mock.constr10 Mock.a)
                                , (Mock.f Mock.a, Mock.g Mock.b)
                                ]
                            ]
                        )
                    ]
                )
                Conditional
                    { term = ()
                    , predicate =
                        makeAndPredicate
                            ( makeEqualsPredicate
                                (Mock.constr10 (mkElemVar Mock.xConfig))
                                (Mock.f (mkElemVar Mock.yConfig))
                            )
                            ( makeEqualsPredicate
                                (Mock.f (mkElemVar Mock.xConfig))
                                (Mock.g Mock.a)
                            )
                    , substitution =
                        Substitution.unsafeWrap
                            [ (inject Mock.yConfig, Mock.b)
                            ]
                    }
        assertEqual "" (MultiOr.singleton expect) actual
    ]

test_simplifyPredicates :: [TestTree]
test_simplifyPredicates =
    [ testCase "\\top => \\top" $ do
        [actual] <- simplifyPredicates MultiAnd.top
        assertEqual "" Condition.top actual
    , testCase "\\bottom and _ => \\bottom" $ do
        let predicate =
                MultiAnd.make
                    [ makeFalsePredicate
                    , makeEqualsPredicate
                        (mkElemVar Mock.xConfig)
                        Mock.a
                    ]
        actual <- simplifyPredicates predicate
        assertEqual "" [] actual
    , testCase "_ and \\bottom => \\bottom" $ do
        let predicate =
                MultiAnd.make
                    [ makeEqualsPredicate
                        (mkElemVar Mock.xConfig)
                        Mock.a
                    , makeFalsePredicate
                    ]
        actual <- simplifyPredicates predicate
        assertEqual "" [] actual
    ]

simplify ::
    Condition RewritingVariableName ->
    IO (OrCondition RewritingVariableName)
simplify condition = runSimplifier mempty condition

runSimplifier ::
    BuiltinAndAxiomSimplifierMap ->
    Condition RewritingVariableName ->
    IO (OrCondition RewritingVariableName)
runSimplifier patternSimplifierMap predicate =
    fmap MultiOr.make $
        Test.runSimplifierBranch env $
            simplifier SideCondition.top predicate
  where
    env = Mock.env{Test.simplifierAxioms = patternSimplifierMap}
    ConditionSimplifier simplifier =
        Condition.create SubstitutionSimplifier.substitutionSimplifier

simplificationEvaluator ::
    [BuiltinAndAxiomSimplifier] ->
    BuiltinAndAxiomSimplifier
simplificationEvaluator = firstFullEvaluation

makeEvaluator ::
    ( forall variable.
      InternalVariable variable =>
      [(TermLike variable, TermLike variable)]
    ) ->
    BuiltinAndAxiomSimplifier
makeEvaluator mapping = BuiltinAndAxiomSimplifier $ simpleEvaluator mapping

simpleEvaluator ::
    MonadSimplify simplifier =>
    [(TermLike RewritingVariableName, TermLike RewritingVariableName)] ->
    TermLike RewritingVariableName ->
    SideCondition RewritingVariableName ->
    simplifier (AttemptedAxiom RewritingVariableName)
simpleEvaluator [] _ _ = return NotApplicable
simpleEvaluator ((fromTermLike, toTermLike) : ps) patt sideCondition
    | fromTermLike == patt =
        return $
            Applied
                AttemptedAxiomResults
                    { results = OrPattern.fromTermLike toTermLike
                    , remainders = OrPattern.bottom
                    }
    | otherwise =
        simpleEvaluator ps patt sideCondition

simplifyPredicates ::
    MultiAnd (Predicate RewritingVariableName) ->
    IO [Condition RewritingVariableName]
simplifyPredicates predicate =
    Condition.simplifyPredicates SideCondition.top predicate
        & Test.runSimplifierBranch Mock.env
