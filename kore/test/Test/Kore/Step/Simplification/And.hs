module Test.Kore.Step.Simplification.And
    ( test_andSimplification
    ) where

import Prelude.Kore

import Test.Tasty

import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.MultiAnd as MultiAnd
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( makeAndPredicate
    , makeCeilPredicate
    , makeCeilPredicate
    , makeEqualsPredicate
    , makeEqualsPredicate
    , makeExistsPredicate
    , makeFalsePredicate
    , makeImpliesPredicate
    , makeNotPredicate
    , makeTruePredicate
    , makeTruePredicate
    )
import qualified Kore.Internal.SideCondition as SideCondition
    ( top
    )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
import Kore.Step.Simplification.And
import qualified Kore.Step.Simplification.Not as Not

import Test.Kore.Step.MockSymbols
    ( testSort
    )
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext

test_andSimplification :: [TestTree]
test_andSimplification =
    [ testCase "And truth table" $ do
        assertEqual "false and false = false"
            OrPattern.bottom
            =<< evaluate (makeAnd [] [])
        assertEqual "false and true = false"
            OrPattern.bottom
            =<< evaluate (makeAnd [] [Pattern.top])
        assertEqual "true and false = false"
            OrPattern.bottom
            =<< evaluate (makeAnd [Pattern.top] [])
        assertEqual "true and true = true"
            OrPattern.top
            =<< evaluate (makeAnd [Pattern.top] [Pattern.top])

    , testCase "And with booleans" $ do
        assertEqual "false and something = false"
            OrPattern.bottom
            =<< evaluate (makeAnd [] [fOfXExpanded])
        assertEqual "something and false = false"
            OrPattern.bottom
            =<< evaluate (makeAnd [fOfXExpanded] [])
        assertEqual "true and something = something"
            (OrPattern.fromPatterns [fOfXExpanded])
            =<< evaluate (makeAnd [Pattern.top] [fOfXExpanded])
        assertEqual "something and true = something"
            (OrPattern.fromPatterns [fOfXExpanded])
            =<< evaluate (makeAnd [fOfXExpanded] [Pattern.top])

    , testCase "And with partial booleans" $ do
        assertEqual "false term and something = false"
            mempty
            =<< evaluatePatterns bottomTerm fOfXExpanded
        assertEqual "something and false term = false"
            mempty
            =<< evaluatePatterns fOfXExpanded bottomTerm
        assertEqual "false predicate and something = false"
            mempty
            =<< evaluatePatterns falsePredicate fOfXExpanded
        assertEqual "something and false predicate = false"
            mempty
            =<< evaluatePatterns fOfXExpanded falsePredicate

    , testGroup "And with normal patterns"
        [ testCase "And random terms" $ do
            let expect =
                    Conditional
                        { term = mkAnd plain0OfX plain1OfX
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            actual <- evaluatePatterns plain0OfXExpanded plain1OfXExpanded
            assertEqual "" (OrPattern.fromPatterns [expect]) actual

        , testCase "And function terms" $ do
            let expect =
                    makeEqualsPredicate fOfX gOfX
                    & Condition.fromPredicate
                    & Pattern.withCondition fOfX
            actual <- evaluatePatterns fOfXExpanded gOfXExpanded
            assertEqual "" (OrPattern.fromPatterns [expect]) actual

        , testCase "And predicates" $ do
            let expect =
                    Conditional
                        { term = mkTop_
                        , predicate =
                            makeAndPredicate
                                (makeCeilPredicate fOfX)
                                (makeCeilPredicate gOfX)
                        , substitution = mempty
                        }
            actual <-
                evaluatePatterns
                    Conditional
                        { term = mkTop_
                        , predicate = makeCeilPredicate fOfX
                        , substitution = mempty
                        }
                    Conditional
                        { term = mkTop_
                        , predicate = makeCeilPredicate gOfX
                        , substitution = mempty
                        }
            assertEqual "" (OrPattern.fromPatterns [expect]) actual

        , testCase "And substitutions - simple" $ do
            let expect =
                    Conditional
                        { term = mkTop_
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [(inject Mock.y, fOfX), (inject Mock.z, gOfX)]
                        }
            actual <-
                evaluatePatterns
                    Conditional
                        { term = mkTop_
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.wrap
                            $ Substitution.mkUnwrappedSubstitution
                            [(inject Mock.y, fOfX)]
                        }
                    Conditional
                        { term = mkTop_
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.wrap
                            $ Substitution.mkUnwrappedSubstitution
                            [(inject Mock.z, gOfX)]
                        }
            assertEqual "" (OrPattern.fromPatterns [expect]) actual

        , testCase "And substitutions - multiple terms" $ do
            let
                expect =
                    Conditional
                        { term = mkAnd (mkAnd Mock.a Mock.b) Mock.c
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            actual <- evaluatePatterns
                Conditional
                    { term = mkAnd Mock.a Mock.b
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                Conditional
                    { term = mkAnd Mock.b Mock.c
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
            assertEqual "" (OrPattern.fromPatterns [expect]) actual

        , testCase "And substitutions - separate predicate" $ do
            let
                expect =
                    Conditional
                        { term = mkTop_
                        , predicate = makeEqualsPredicate fOfX gOfX
                        , substitution =
                            Substitution.unsafeWrap [(inject Mock.y, fOfX)]
                        }
            actual <- evaluatePatterns
                Conditional
                    { term = mkTop_
                    , predicate = makeTruePredicate
                    , substitution =
                        Substitution.wrap
                        $ Substitution.mkUnwrappedSubstitution
                        [(inject Mock.y, fOfX)]
                    }
                Conditional
                    { term = mkTop_
                    , predicate = makeTruePredicate
                    , substitution =
                        Substitution.wrap
                        $ Substitution.mkUnwrappedSubstitution
                        [(inject Mock.y, gOfX)]
                    }
            assertEqual "" (OrPattern.fromPatterns [expect]) actual

        , testCase "And substitutions - failure" $ do
            actual <-
                evaluatePatterns
                    Conditional
                        { term = mkTop_
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap
                            $ Substitution.mkUnwrappedSubstitution
                            [   ( inject Mock.y
                                , Mock.functionalConstr10 (mkElemVar Mock.x)
                                )
                            ]
                        }
                    Conditional
                        { term = mkTop_
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap
                            $ Substitution.mkUnwrappedSubstitution
                            [   ( inject Mock.y
                                , Mock.functionalConstr11 (mkElemVar Mock.x)
                                )
                            ]
                        }
            assertEqual "" OrPattern.bottom actual
            {-
            TODO(virgil): Uncomment this after substitution merge can handle
            function equality.

            assertEqual
                "Combines conditions with substitution merge condition"
                Pattern
                    { term = mkTop_
                    , predicate =
                        fst $ makeAndPredicate
                            (fst $ makeAndPredicate
                                (makeCeilPredicate fOfX)
                                (makeCeilPredicate gOfX)
                            )
                            (givemakeEqualsPredicate fOfX gOfX)
                    , substitution = [(y, fOfX)]
                    }
                (evaluatePatternsWithAttributes
                    [ (fSymbol, mock.functionAttributes)
                    , (gSymbol, mock.functionAttributes)
                    ]
                    Pattern
                        { term = mkTop_
                        , predicate = makeCeilPredicate fOfX
                        , substitution = [(y, fOfX)]
                        }
                    Pattern
                        { term = mkTop_
                        , predicate = makeCeilPredicate gOfX
                        , substitution = [(y, gOfX)]
                        }
                )
            -}
        ]
    , testGroup "Variable-function and"
        [ testCase "variable-term" $ do
            let expect =
                    Conditional
                        { term = fOfX
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [(inject Mock.y, fOfX)]
                        }
            actual <- evaluatePatterns yExpanded fOfXExpanded
            assertEqual "" (MultiOr.make [expect]) actual

        , testCase "term-variable" $ do
            let expect =
                    Conditional
                        { term = fOfX
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [(inject Mock.y, fOfX)]
                        }
            actual <- evaluatePatterns fOfXExpanded yExpanded
            assertEqual "" (MultiOr.make [expect]) actual
        ]

    , testGroup "constructor and"
        [ testCase "same constructors" $ do
            let expect =
                    Conditional
                        { term = Mock.constr10 fOfX
                        , predicate =
                            makeEqualsPredicate fOfX gOfX
                        , substitution = mempty
                        }
            actual <-
                evaluatePatterns Conditional
                        { term = Mock.constr10 fOfX
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    Conditional
                        { term = Mock.constr10 gOfX
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            assertEqual "" (MultiOr.make [expect]) actual

        , testCase "different constructors" $ do
            actual <-
                evaluatePatterns
                    Conditional
                        { term = Mock.constr10 fOfX
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    Conditional
                        { term = Mock.constr11 gOfX
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
            assertEqual "" (MultiOr.make []) actual
        ]

    -- (a or b) and (c or d) = (b and d) or (b and c) or (a and d) or (a and c)
    , testCase "And-Or distribution" $ do
        let expect =
                OrPattern.fromPatterns
                    [ makeEqualsPredicate fOfX gOfX
                        & Condition.fromPredicate
                        & Pattern.withCondition fOfX
                    , Conditional
                        { term = fOfX
                        , predicate = makeCeilPredicate gOfX
                        , substitution = mempty
                        }
                    , Conditional
                        { term = gOfX
                        , predicate = makeCeilPredicate fOfX
                        , substitution = mempty
                        }
                    , Conditional
                        { term = mkTop_
                        , predicate =
                            makeAndPredicate
                                (makeCeilPredicate fOfX)
                                (makeCeilPredicate gOfX)
                        , substitution = mempty
                        }
                    ]
        actual <-
            evaluate
                (makeAnd
                    [ fOfXExpanded
                    , Conditional
                        { term = mkTop_
                        , predicate = makeCeilPredicate fOfX
                        , substitution = mempty
                        }
                    ]
                    [ gOfXExpanded
                    , Conditional
                        { term = mkTop_
                        , predicate = makeCeilPredicate gOfX
                        , substitution = mempty
                        }
                    ]
                )
        assertEqual "Distributes or" expect actual
    , testCase "Predicates are not duplicated" $ do
        let expect =
                Conditional
                    { term = Mock.constr10 fOfX
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate fOfX)
                            (makeEqualsPredicate fOfX gOfX)
                    , substitution = mempty
                    }
        actual <-
            evaluatePatterns
                Conditional
                    { term = Mock.constr10 fOfX
                    , predicate = makeCeilPredicate fOfX
                    , substitution = mempty
                    }
                Conditional
                    { term = Mock.constr10 gOfX
                    , predicate = makeCeilPredicate fOfX
                    , substitution = mempty
                    }
        assertEqual "" (MultiOr.make [expect]) actual
    , testCase "Contradictions result in bottom" $ do
        actual <-
            evaluatePatterns
                Conditional
                    { term = Mock.constr10 fOfX
                    , predicate = makeCeilPredicate fOfX
                    , substitution = mempty
                    }
                Conditional
                    { term = Mock.constr10 fOfX
                    , predicate = makeNotPredicate $ makeCeilPredicate fOfX
                    , substitution = mempty
                    }
        assertEqual "" mempty actual
    , testCase "Simplifies Implies - Positive" $ do
        let expect =
                Conditional
                    { term = Mock.constr10 fOfX
                    , predicate =
                        (MultiAnd.toPredicate . MultiAnd.make)
                        [ makeCeilPredicate fOfX
                        , makeCeilPredicate gOfX
                        , makeEqualsPredicate fOfX gOfX
                        ]
                    , substitution = mempty
                    }
        actual <-
            evaluatePatterns
                Conditional
                    { term = Mock.constr10 fOfX
                    , predicate = makeCeilPredicate fOfX
                    , substitution = mempty
                    }
                Conditional
                    { term = Mock.constr10 gOfX
                    , predicate = makeImpliesPredicate
                        (makeCeilPredicate fOfX)
                        (makeCeilPredicate gOfX)
                    , substitution = mempty
                    }
        assertEqual "" (MultiOr.make [expect]) actual
    , testCase "Simplifies Implies - Negative" $ do
        let expect =
                Conditional
                    { term = Mock.constr10 fOfX
                    , predicate =
                        makeAndPredicate
                            (makeEqualsPredicate fOfX gOfX)
                            (makeNotPredicate $ makeCeilPredicate fOfX)
                    , substitution = mempty
                    }
        actual <-
            evaluatePatterns
                Conditional
                    { term = Mock.constr10 fOfX
                    , predicate = makeNotPredicate $ makeCeilPredicate fOfX
                    , substitution = mempty
                    }
                Conditional
                    { term = Mock.constr10 gOfX
                    , predicate =
                        makeImpliesPredicate
                            (makeCeilPredicate fOfX)
                            (makeCeilPredicate gOfX)
                    , substitution = mempty
                    }
        assertEqual "" (MultiOr.make [expect]) actual
    , testCase "Simplifies multiple Implies" $ do
        let expect =
                Conditional
                    { term = Mock.constr10 fOfX
                    , predicate =
                        (MultiAnd.toPredicate . MultiAnd.make)
                        [ makeCeilPredicate fOfX
                        , makeCeilPredicate fOfY
                        , makeCeilPredicate gOfX
                        , makeEqualsPredicate fOfX gOfX
                        ]
                    , substitution = mempty
                    }
        actual <-
            evaluatePatterns
                Conditional
                    { term = Mock.constr10 fOfX
                    , predicate = makeCeilPredicate fOfX
                    , substitution = mempty
                    }
                Conditional
                    { term = Mock.constr10 gOfX
                    , predicate =
                        makeAndPredicate
                            (makeImpliesPredicate
                                (makeCeilPredicate fOfX)
                                (makeCeilPredicate gOfX)
                            )
                            (makeImpliesPredicate
                                (makeCeilPredicate gOfX)
                                (makeCeilPredicate fOfY)
                            )
                    , substitution = mempty
                    }
        assertEqual "" (MultiOr.make [expect]) actual
    , testCase "Does not replace and terms under intersecting quantifiers" $ do
        let expect =
                Conditional
                    { term = Mock.constr10 fOfX
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate fOfX)
                            (makeExistsPredicate Mock.x
                                (makeCeilPredicate fOfX)
                            )
                    , substitution = mempty
                    }
        actual <-
            evaluatePatterns
                Conditional
                    { term = Mock.constr10 fOfX
                    , predicate = makeCeilPredicate fOfX
                    , substitution = mempty
                    }
                Conditional
                    { term = Mock.constr10 fOfX
                    , predicate =
                        makeExistsPredicate Mock.x (makeCeilPredicate fOfX)
                    , substitution = mempty
                    }
        assertEqual "" (MultiOr.make [expect]) actual
    , testCase "Replaces and terms under independent quantifiers" $ do
        let expect =
                Conditional
                    { term = Mock.constr10 fOfX
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate fOfX)
                            (makeExistsPredicate Mock.y
                                (makeCeilPredicate fOfY)
                            )
                    , substitution = mempty
                    }
        actual <-
            evaluatePatterns
                Conditional
                    { term = Mock.constr10 fOfX
                    , predicate = makeCeilPredicate fOfX
                    , substitution = mempty
                    }
                Conditional
                    { term = Mock.constr10 fOfX
                    , predicate =
                        makeExistsPredicate Mock.y
                            (makeAndPredicate
                                (makeCeilPredicate fOfX)
                                (makeCeilPredicate fOfY)
                            )
                    , substitution = mempty
                    }
        assertEqual "" (MultiOr.make [expect]) actual
    , testGroup "Local function evaluation" $
        let f = Mock.f (mkElemVar Mock.x)
            fInt = Mock.fInt (mkElemVar Mock.xInt)
            defined = makeCeilPredicate_ f & Condition.fromPredicate
            a = Mock.a
            b = Mock.b
            injA = Mock.sortInjection10 Mock.a
            injB = Mock.sortInjection10 Mock.b
            int2 = Mock.builtinInt 2
            int3 = Mock.builtinInt 3
            mkLocalDefn func (Left t)  = makeEqualsPredicate_ t func
            mkLocalDefn func (Right t) = makeEqualsPredicate_ func t
            test name func eitherC1 eitherC2 =
                testCase name $ do
                    let equals1 = mkLocalDefn func eitherC1 & Condition.fromPredicate
                        equals2 = mkLocalDefn func eitherC2 & Condition.fromPredicate
                        pattern1 = Pattern.fromCondition_ (defined <> equals1)
                        pattern2 = Pattern.fromCondition_ (defined <> equals2)
                    actual <- evaluatePatterns pattern1 pattern2
                    assertBool "Expected \\bottom" $ isBottom actual
        in
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
            -- Builtin at top
            , test "contradiction: f(x) = 2 ∧ f(x) = 3" fInt (Right int2) (Right int3)
            , test "contradiction: 2 = f(x) ∧ f(x) = 3" fInt (Left  int2) (Right int3)
            , test "contradiction: 2 = f(x) ∧ 3 = f(x)" fInt (Left  int2) (Left  int3)
            , test "contradiction: f(x) = 2 ∧ 3 = f(x)" fInt (Right int2) (Left  int3)
            ]
    ]
  where
    yExpanded = Conditional
        { term = mkElemVar Mock.y
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    fOfX = Mock.f (mkElemVar Mock.x)
    fOfXExpanded = Pattern.fromTermLike fOfX
    fOfY = Mock.f (mkElemVar Mock.y)
    gOfX = Mock.g (mkElemVar Mock.x)
    gOfXExpanded = Conditional
        { term = gOfX
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    plain0OfX = Mock.plain10 (mkElemVar Mock.x)
    plain0OfXExpanded = Conditional
        { term = plain0OfX
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    plain1OfX = Mock.plain11 (mkElemVar Mock.x)
    plain1OfXExpanded = Conditional
        { term = plain1OfX
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    bottomTerm = Conditional
        { term = mkBottom_
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    falsePredicate = Conditional
        { term = mkTop_
        , predicate = makeFalsePredicate
        , substitution = mempty
        }

makeAnd
    :: [Pattern VariableName]
    -> [Pattern VariableName]
    -> And Sort (OrPattern VariableName)
makeAnd first second =
    And
        { andSort = findSort (first ++ second)
        , andFirst = OrPattern.fromPatterns first
        , andSecond = OrPattern.fromPatterns second
        }

findSort :: [Pattern VariableName] -> Sort
findSort [] = testSort
findSort ( Conditional {term} : _ ) = termLikeSort term

evaluate :: And Sort (OrPattern VariableName) -> IO (OrPattern VariableName)
evaluate And { andFirst, andSecond } =
    MultiAnd.make [andFirst, andSecond]
    & simplify Not.notSimplifier SideCondition.top
    & runSimplifier Mock.env

evaluatePatterns
    :: Pattern VariableName
    -> Pattern VariableName
    -> IO (OrPattern VariableName)
evaluatePatterns first second =
    MultiAnd.make [first, second]
    & makeEvaluate Not.notSimplifier SideCondition.top
    & runSimplifierBranch Mock.env
    & fmap OrPattern.fromPatterns
