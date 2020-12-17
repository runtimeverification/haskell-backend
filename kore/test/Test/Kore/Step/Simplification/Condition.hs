module Test.Kore.Step.Simplification.Condition
    ( test_simplify_local_functions
    , test_predicateSimplification
    ) where

import Prelude.Kore

import Test.Tasty

import qualified Data.Map.Strict as Map

import Kore.Internal.Condition
    ( Condition
    , Conditional (..)
    )
import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.Condition as Conditional
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrCondition
    ( OrCondition
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Predicate
    ( makeAndPredicate
    , makeCeilPredicate_
    , makeEqualsPredicate_
    , makeTruePredicate_
    )
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.SideCondition as SideCondition
    ( top
    )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
import Kore.Step.Axiom.EvaluationStrategy
    ( firstFullEvaluation
    )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
    ( AxiomIdentifier (..)
    )
import qualified Kore.Step.Simplification.Condition as Condition
import Kore.Step.Simplification.Simplify
import qualified Kore.Step.Simplification.SubstitutionSimplifier as SubstitutionSimplifier
import Kore.TopBottom

import qualified Test.Kore.Step.MockSymbols as Mock
import qualified Test.Kore.Step.Simplification as Test
import Test.Tasty.HUnit.Ext

test_simplify_local_functions :: [TestTree]
test_simplify_local_functions =
    [ -- Constructor at top
      test "contradiction: f(x) = a ∧ f(x) = b" f (Right a) (Right b)
    , test "contradiction: a = f(x) ∧ f(x) = b" f (Left  a) (Right b)
    , test "contradiction: a = f(x) ∧ b = f(x)" f (Left  a) (Left  b)
    , test "contradiction: f(x) = a ∧ b = f(x)" f (Right a) (Left  b)
    -- Sort injection at top
    , test "contradiction: f(x) = injA ∧ f(x) = injB" f (Right injA) (Right injB)
    , test "contradiction: injA = f(x) ∧ f(x) = injB" f (Left  injA) (Right injB)
    , test "contradiction: injA = f(x) ∧ injB = f(x)" f (Left  injA) (Left  injB)
    , test "contradiction: f(x) = injA ∧ injB = f(x)" f (Right injA) (Left  injB)
    -- Int at top
    , test "contradiction: f(x) = 2 ∧ f(x) = 3" fInt (Right int2) (Right int3)
    , test "contradiction: 2 = f(x) ∧ f(x) = 3" fInt (Left  int2) (Right int3)
    , test "contradiction: 2 = f(x) ∧ 3 = f(x)" fInt (Left  int2) (Left  int3)
    , test "contradiction: f(x) = 2 ∧ 3 = f(x)" fInt (Right int2) (Left  int3)
    -- Bool at top
    , test "contradiction: f(x) = true ∧ f(x) = false" fBool (Right boolTrue) (Right boolFalse)
    , test "contradiction: true = f(x) ∧ f(x) = false" fBool (Left  boolTrue) (Right boolFalse)
    , test "contradiction: true = f(x) ∧ false = f(x)" fBool (Left  boolTrue) (Left  boolFalse)
    , test "contradiction: f(x) = true ∧ false = f(x)" fBool (Right boolTrue) (Left  boolFalse)
    -- String at top
    , test "contradiction: f(x) = \"one\" ∧ f(x) = \"two\"" fString (Right strOne) (Right strTwo)
    , test "contradiction: \"one\" = f(x) ∧ f(x) = \"two\"" fString (Left  strOne) (Right strTwo)
    , test "contradiction: \"one\" = f(x) ∧ \"two\" = f(x)" fString (Left  strOne) (Left  strTwo)
    , test "contradiction: f(x) = \"one\" ∧ \"two\" = f(x)" fString (Right strOne) (Left  strTwo)
    ]
  where
    f = Mock.f (mkElemVar Mock.x)
    fInt = Mock.fInt (mkElemVar Mock.xInt)
    fBool = Mock.fBool (mkElemVar Mock.xBool)
    fString = Mock.fString (mkElemVar Mock.xString)
    defined = makeCeilPredicate_ f & Condition.fromPredicate

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

    mkLocalDefn func (Left t)  = makeEqualsPredicate_ t func
    mkLocalDefn func (Right t) = makeEqualsPredicate_ func t

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
        assertEqual ""
            (MultiOr.singleton Conditional.topCondition)
            actualTop

    , testCase "Applies substitution to predicate" $ do
        let expect =
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate_
                            (Mock.f Mock.a)
                            (Mock.g Mock.b)
                    , substitution = Substitution.unsafeWrap
                        [ (inject Mock.x, Mock.a)
                        , (inject Mock.y, Mock.b)
                        ]
                    }
        actual <-
            runSimplifier Map.empty
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate_
                            (Mock.f (mkElemVar Mock.x))
                            (Mock.g (mkElemVar Mock.y))
                    , substitution = Substitution.unsafeWrap
                        [ (inject Mock.x, Mock.a)
                        , (inject Mock.y, Mock.b)
                        ]
                    }
        assertEqual "" (MultiOr.singleton expect) actual

    , testCase "Simplifies predicate after substitution" $ do
        let expect =
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate_
                            Mock.functional00
                            Mock.functional01
                    , substitution = Substitution.unsafeWrap
                        [ (inject Mock.x, Mock.functional00)
                        , (inject Mock.y, Mock.functional01)
                        ]
                    }
        actual <-
            runSimplifier Map.empty
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate_
                            (Mock.constr10 (mkElemVar Mock.x))
                            (Mock.constr10 (mkElemVar Mock.y))
                    , substitution = Substitution.unsafeWrap
                        [ (inject Mock.x, Mock.functional00)
                        , (inject Mock.y, Mock.functional01)
                        ]
                    }
        assertEqual "" (MultiOr.singleton expect) actual

    , testCase "Simplifies predicate after substitution" $ do
        let expect =
                Conditional
                    { term = ()
                    , predicate = makeEqualsPredicate_ Mock.a Mock.functional00
                    , substitution = Substitution.unsafeWrap
                        [ (inject Mock.x, Mock.functional00)
                        , (inject Mock.y, Mock.functional01)
                        ]
                    }
        actual <-
            runSimplifier
                (Map.fromList
                    [   ( AxiomIdentifier.Application Mock.fId
                        , simplificationEvaluator
                            [ makeEvaluator
                                [   ( Mock.f Mock.functional00
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
                        makeEqualsPredicate_
                            (Mock.f (mkElemVar Mock.x))
                            (Mock.f (mkElemVar Mock.y))
                    , substitution = Substitution.unsafeWrap
                        [ (inject Mock.x, Mock.functional00)
                        , (inject Mock.y, Mock.functional01)
                        ]
                    }
        assertEqual "" (MultiOr.singleton expect) actual

    , testCase "Merges substitution from predicate simplification" $ do
        let expect =
                Conditional
                    { term = ()
                    , predicate = makeTruePredicate_
                    , substitution = Substitution.unsafeWrap
                        [ (inject Mock.x, Mock.a)
                        , (inject Mock.y, Mock.b)
                        ]
                    }
        actual <-
            runSimplifier
                (Map.fromList
                    [   ( AxiomIdentifier.Application Mock.fId
                        , simplificationEvaluator
                            [ makeEvaluator
                                [ (Mock.f Mock.b, Mock.constr10 Mock.a) ]
                            ]
                        )
                    ]
                )
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate_
                            (Mock.constr10 (mkElemVar Mock.x))
                            (Mock.f (mkElemVar Mock.y))
                    , substitution = Substitution.unsafeWrap
                        [ (inject Mock.y, Mock.b)
                        ]
                    }
        assertEqual "" (MultiOr.singleton expect) actual

    , testCase "Reapplies substitution from predicate simplification" $ do
        let expect =
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate_
                            (Mock.f Mock.a)
                            (Mock.g Mock.a)
                    , substitution = Substitution.unsafeWrap
                        [ (inject Mock.x, Mock.a)
                        , (inject Mock.y, Mock.b)
                        ]
                    }
        actual <-
            runSimplifier
                (Map.fromList
                    [   ( AxiomIdentifier.Application Mock.fId
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
                            (makeEqualsPredicate_
                                (Mock.constr10 (mkElemVar Mock.x))
                                (Mock.f (mkElemVar Mock.y))
                            )
                            (makeEqualsPredicate_
                                (Mock.f (mkElemVar Mock.x))
                                (Mock.g Mock.a)
                            )
                    , substitution = Substitution.unsafeWrap
                        [ (inject Mock.y, Mock.b)
                        ]
                    }
        assertEqual "" (MultiOr.singleton expect) actual

    , testCase "Simplifies after reapplying substitution" $ do
        let expect =
                Conditional
                    { term = ()
                    , predicate =
                        makeEqualsPredicate_
                            (Mock.g Mock.a)
                            (Mock.g Mock.b)
                    , substitution = Substitution.unsafeWrap
                        [ (inject Mock.x, Mock.a)
                        , (inject Mock.y, Mock.b)
                        ]
                    }
        actual <-
            runSimplifier
                (Map.fromList
                    [   ( AxiomIdentifier.Application Mock.fId
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
                            (makeEqualsPredicate_
                                (Mock.constr10 (mkElemVar Mock.x))
                                (Mock.f (mkElemVar Mock.y))
                            )
                            (makeEqualsPredicate_
                                (Mock.f (mkElemVar Mock.x))
                                (Mock.g Mock.a)
                            )
                    , substitution = Substitution.unsafeWrap
                        [ (inject Mock.y, Mock.b)
                        ]
                    }
        assertEqual "" (MultiOr.singleton expect) actual
    ]

simplify :: Condition VariableName -> IO (OrCondition VariableName)
simplify condition = runSimplifier mempty condition

runSimplifier
    :: BuiltinAndAxiomSimplifierMap
    -> Condition VariableName
    -> IO (OrCondition VariableName)
runSimplifier patternSimplifierMap predicate =
    fmap MultiOr.make
    $ Test.runSimplifierBranch env
    $ simplifier SideCondition.top predicate
  where
    env = Mock.env { Test.simplifierAxioms = patternSimplifierMap }
    ConditionSimplifier simplifier =
        Condition.create SubstitutionSimplifier.substitutionSimplifier

simplificationEvaluator
    :: [BuiltinAndAxiomSimplifier]
    -> BuiltinAndAxiomSimplifier
simplificationEvaluator = firstFullEvaluation

makeEvaluator
    :: (forall variable. InternalVariable variable
        => [(TermLike variable, TermLike variable)]
        )
    -> BuiltinAndAxiomSimplifier
makeEvaluator mapping = BuiltinAndAxiomSimplifier $ simpleEvaluator mapping

simpleEvaluator
    :: (InternalVariable variable, MonadSimplify simplifier)
    => [(TermLike variable, TermLike variable)]
    -> TermLike variable
    -> SideCondition variable
    -> simplifier (AttemptedAxiom variable)
simpleEvaluator [] _  _ = return NotApplicable
simpleEvaluator ((fromTermLike, toTermLike) : ps) patt sideCondition
  | fromTermLike == patt =
    return $ Applied AttemptedAxiomResults
        { results = OrPattern.fromTermLike toTermLike
        , remainders = OrPattern.bottom
        }
  | otherwise =
    simpleEvaluator ps patt sideCondition
