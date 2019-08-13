module Test.Kore.Step.Function.Integration
    ( test_functionIntegration
    , test_Nat
    , test_List
    , test_Map
    , test_Pair
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Control.Lens as Lens
import           Data.Function
import           Data.Generics.Product
import qualified Data.Map as Map
import           Data.Maybe
import           Prelude hiding
                 ( succ )

import           Data.Sup
import qualified Kore.Builtin.AssociativeCommutative as Ac
import qualified Kore.Builtin.Int as Int
                 ( builtinFunctions )
import qualified Kore.Builtin.Map as Map
                 ( builtinFunctions )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern as Pattern
import           Kore.Internal.Symbol
import           Kore.Internal.TermLike
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeCeilPredicate, makeEqualsPredicate,
                 makeTruePredicate )
import qualified Kore.Predicate.Predicate as Syntax
                 ( Predicate )
import           Kore.Step.Axiom.EvaluationStrategy
                 ( builtinEvaluation, definitionEvaluation,
                 firstFullEvaluation, simplifierWithFallback )
import           Kore.Step.Axiom.Identifier
                 ( AxiomIdentifier )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
import           Kore.Step.Axiom.UserDefined
                 ( equalityRuleEvaluator )
import           Kore.Step.Rule
                 ( EqualityRule (..) )
import           Kore.Step.Rule as RulePattern
                 ( RulePattern (..), rulePattern )
import           Kore.Step.Simplification.Data
import           Kore.Step.Simplification.Data as AttemptedAxiom
                 ( AttemptedAxiom (..) )
import qualified Kore.Step.Simplification.TermLike as TermLike
                 ( simplify )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Variables.Fresh
import           Kore.Variables.UnifiedVariable
                 ( UnifiedVariable (..) )
import qualified SMT

import           Test.Kore
import qualified Test.Kore.Builtin.Builtin as Builtin
import qualified Test.Kore.Builtin.Definition as Builtin
import qualified Test.Kore.Builtin.Int as Int
import qualified Test.Kore.Builtin.List as List
import qualified Test.Kore.Builtin.Map as Map
import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.Axiom.EvaluationStrategy as Axiom
                 ( evaluate )
import           Test.Kore.Step.Axiom.Matcher
                 ( doesn'tMatch, matches )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_functionIntegration :: [TestTree]
test_functionIntegration =
    [ testCase "Simple evaluation" $ do
        let expect =
                Conditional
                    { term = Mock.g Mock.c
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                (Map.singleton
                    (AxiomIdentifier.Application Mock.functionalConstr10Id)
                    (axiomEvaluator
                        (Mock.functionalConstr10 (mkElemVar Mock.x))
                        (Mock.g (mkElemVar Mock.x))
                    )
                )
                (Mock.functionalConstr10 Mock.c)
        assertEqualWithExplanation "" expect actual

    , testCase "Simple evaluation (builtin branch)" $ do
        let expect =
                Conditional
                    { term = Mock.g Mock.c
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                (Map.singleton
                    (AxiomIdentifier.Application Mock.functionalConstr10Id)
                    (builtinEvaluation $ axiomEvaluator
                        (Mock.functionalConstr10 (mkElemVar Mock.x))
                        (Mock.g (mkElemVar Mock.x))
                    )
                )
                (Mock.functionalConstr10 Mock.c)
        assertEqualWithExplanation "" expect actual

    , testCase "Simple evaluation (Axioms & Builtin branch, Builtin works)"
      $ do
        let expect =
                Conditional
                    { term = Mock.g Mock.c
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                (Map.singleton
                    (AxiomIdentifier.Application Mock.functionalConstr10Id)
                    (simplifierWithFallback
                        (builtinEvaluation $ axiomEvaluator
                            (Mock.functionalConstr10 (mkElemVar Mock.x))
                            (Mock.g (mkElemVar Mock.x))
                        )
                        ( axiomEvaluator
                            (Mock.functionalConstr10 (mkElemVar Mock.x))
                            (mkElemVar Mock.x)
                        )
                    )
                )
                (Mock.functionalConstr10 Mock.c)
        assertEqualWithExplanation "" expect actual

    , testCase "Simple evaluation (Axioms & Builtin branch, Builtin fails)"
      $ do
        let expect =
                Conditional
                    { term = Mock.g Mock.c
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                (Map.singleton
                    (AxiomIdentifier.Application Mock.functionalConstr10Id)
                    (simplifierWithFallback
                        (builtinEvaluation $ BuiltinAndAxiomSimplifier
                            (\_ _ _ _ -> notApplicableAxiomEvaluator)
                        )
                        ( axiomEvaluator
                            (Mock.functionalConstr10 (mkElemVar Mock.x))
                            (Mock.g (mkElemVar Mock.x))
                        )
                    )
                )
                (Mock.functionalConstr10 Mock.c)
        assertEqualWithExplanation "" expect actual

    , testCase "Evaluates inside functions" $ do
        let expect =
                Conditional
                    { term = Mock.functional10 (Mock.functional10 Mock.c)
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                (Map.singleton
                    (AxiomIdentifier.Application Mock.functionalConstr10Id)
                    ( axiomEvaluator
                        (Mock.functionalConstr10 (mkElemVar Mock.x))
                        (Mock.functional10 (mkElemVar Mock.x))
                    )
                )
                (Mock.functionalConstr10 (Mock.functionalConstr10 Mock.c))
        assertEqualWithExplanation "" expect actual

    , testCase "Evaluates 'or'" $ do
        let expect =
                Conditional
                    { term =
                        mkOr
                            (Mock.functional10 (Mock.functional10 Mock.c))
                            (Mock.functional10 (Mock.functional10 Mock.d))
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                (Map.singleton
                    (AxiomIdentifier.Application Mock.functionalConstr10Id)
                    ( axiomEvaluator
                        (Mock.functionalConstr10 (mkElemVar Mock.x))
                        (Mock.functional10 (mkElemVar Mock.x))
                    )
                )
                (Mock.functionalConstr10
                    (mkOr
                        (Mock.functionalConstr10 Mock.c)
                        (Mock.functionalConstr10 Mock.d)
                    )
                )
        assertEqualWithExplanation "" expect actual

    , testCase "Evaluates on multiple branches" $ do
        let expect =
                Conditional
                    { term =
                        Mock.functional10
                            (Mock.functional20
                                (Mock.functional10 Mock.c)
                                (Mock.functional10 Mock.c)
                            )
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                (Map.singleton
                    (AxiomIdentifier.Application Mock.functionalConstr10Id)
                    ( axiomEvaluator
                        (Mock.functionalConstr10 (mkElemVar Mock.x))
                        (Mock.functional10 (mkElemVar Mock.x))
                    )
                )
                (Mock.functionalConstr10
                    (Mock.functional20
                        (Mock.functionalConstr10 Mock.c)
                        (Mock.functionalConstr10 Mock.c)
                    )
                )
        assertEqualWithExplanation "" expect actual

    , testCase "Returns conditions" $ do
        let expect =
                Conditional
                    { term = Mock.f Mock.d
                    , predicate = makeCeilPredicate (Mock.plain10 Mock.e)
                    , substitution = mempty
                    }
        actual <-
            evaluate
                (Map.singleton
                    (AxiomIdentifier.Application Mock.cId)
                    ( appliedMockEvaluator Conditional
                        { term   = Mock.d
                        , predicate = makeCeilPredicate (Mock.plain10 Mock.e)
                        , substitution = mempty
                        }
                    )
                )
                (Mock.f Mock.c)
        assertEqualWithExplanation "" expect actual

    , testCase "Merges conditions" $ do
        let expect =
                Conditional
                    { term = Mock.functional11 (Mock.functional20 Mock.e Mock.e)
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate Mock.cg)
                            (makeCeilPredicate Mock.cf)
                    , substitution = mempty
                    }
        actual <-
            evaluate
                (Map.fromList
                    [   ( AxiomIdentifier.Application Mock.cId
                        , appliedMockEvaluator Conditional
                            { term = Mock.e
                            , predicate = makeCeilPredicate Mock.cg
                            , substitution = mempty
                            }
                        )
                    ,   ( AxiomIdentifier.Application Mock.dId
                        , appliedMockEvaluator Conditional
                            { term = Mock.e
                            , predicate = makeCeilPredicate Mock.cf
                            , substitution = mempty
                            }
                        )
                    ,   ( AxiomIdentifier.Application Mock.functionalConstr10Id
                        , axiomEvaluator
                            (Mock.functionalConstr10 (mkElemVar Mock.x))
                            (Mock.functional11 (mkElemVar Mock.x))
                        )
                    ]
                )
                (Mock.functionalConstr10 (Mock.functional20 Mock.c Mock.d))
        assertEqualWithExplanation "" expect actual

    , testCase "Reevaluates user-defined function results." $ do
        let expect =
                Conditional
                    { term = Mock.f Mock.e
                    , predicate = makeEqualsPredicate (Mock.f Mock.e) Mock.e
                    , substitution = mempty
                    }
        actual <-
            evaluate
                (Map.fromList
                    [   ( AxiomIdentifier.Application Mock.cId
                        , axiomEvaluator Mock.c Mock.d
                        )
                    ,   ( AxiomIdentifier.Application Mock.dId
                        , appliedMockEvaluator Conditional
                            { term = Mock.e
                            , predicate =
                                makeEqualsPredicate (Mock.f Mock.e) Mock.e
                            , substitution = mempty
                            }
                        )
                    ]
                )
                (Mock.f Mock.c)
        assertEqualWithExplanation "" expect actual

    , testCase "Merges substitutions with reevaluation ones." $ do
        let expect =
                Conditional
                    { term = Mock.f Mock.e
                    , predicate = makeTruePredicate
                    , substitution = Substitution.unsafeWrap
                        [   ( ElemVar Mock.var_x_1
                            , Mock.a
                            )
                        ,   ( ElemVar Mock.var_z_1
                            , Mock.a
                            )
                        ]
                    }
        actual <-
            evaluate
                (Map.fromList
                    [   ( AxiomIdentifier.Application Mock.cId
                        , appliedMockEvaluator Conditional
                            { term = Mock.d
                            , predicate = makeTruePredicate
                            , substitution = Substitution.unsafeWrap
                                [   ( ElemVar Mock.x
                                    , mkElemVar Mock.z
                                    )
                                ]
                            }
                        )
                    ,   ( AxiomIdentifier.Application Mock.dId
                        , appliedMockEvaluator Conditional
                            { term = Mock.e
                            , predicate = makeTruePredicate
                            , substitution = Substitution.unsafeWrap
                                [   ( ElemVar Mock.x
                                    , Mock.a
                                    )
                                ]
                            }
                        )
                    ]
                )
                (Mock.f Mock.c)
        assertEqualWithExplanation "" expect actual

    , testCase "Simplifies substitution-predicate." $ do
        -- Mock.plain10 below prevents:
        -- 1. unification without substitution.
        -- 2. Transforming the 'and' in an equals predicate,
        --    as it would happen for functions.
        let expect =
                Conditional
                    { term = Mock.a
                    , predicate =
                        makeCeilPredicate
                            (Mock.plain10 Mock.cf)
                    , substitution = Substitution.unsafeWrap
                        [ (ElemVar Mock.var_x_1, Mock.cf)
                        , (ElemVar Mock.var_y_1, Mock.b)
                        ]
                    }
        actual <-
            evaluate
                (Map.fromList
                    [   ( AxiomIdentifier.Application Mock.fId
                        , appliedMockEvaluator Conditional
                            { term = Mock.a
                            , predicate =
                                makeCeilPredicate
                                    (mkAnd
                                        (Mock.constr20
                                            (Mock.plain10 Mock.cf)
                                            Mock.b
                                        )
                                        (Mock.constr20
                                            (Mock.plain10 (mkElemVar Mock.x))
                                            (mkElemVar Mock.y)
                                        )
                                    )
                            , substitution =
                                Substitution.wrap [(ElemVar Mock.x, Mock.cf)]
                            }
                        )
                    ]
                )
                (Mock.f (mkElemVar Mock.x))
        assertEqualWithExplanation "" expect actual

    , testCase "Evaluates only simplifications." $ do
        let expect =
                Conditional
                    { term = Mock.b
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                (Map.fromList
                    [   ( AxiomIdentifier.Application Mock.fId
                        , simplifierWithFallback
                            (appliedMockEvaluator Conditional
                                { term = Mock.b
                                , predicate = makeTruePredicate
                                , substitution = mempty
                                }
                            )
                            (definitionEvaluation
                                [ axiom
                                    (Mock.f (mkElemVar Mock.y))
                                    Mock.a
                                    makeTruePredicate
                                ]
                            )
                        )
                    ]
                )
                (Mock.f (mkElemVar Mock.x))
        assertEqualWithExplanation "" expect actual

    , testCase "Picks first matching simplification." $ do
        let expect =
                Conditional
                    { term = Mock.b
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                (Map.fromList
                    [   ( AxiomIdentifier.Application Mock.fId
                        , simplifierWithFallback
                            (firstFullEvaluation
                                [ axiomEvaluator
                                    (Mock.f (Mock.g (mkElemVar Mock.x)))
                                    Mock.c
                                ,  appliedMockEvaluator Conditional
                                    { term = Mock.b
                                    , predicate = makeTruePredicate
                                    , substitution = mempty
                                    }
                                ,  appliedMockEvaluator Conditional
                                    { term = Mock.c
                                    , predicate = makeTruePredicate
                                    , substitution = mempty
                                    }
                                ]
                            )
                            (definitionEvaluation
                                [ axiom
                                    (Mock.f (mkElemVar Mock.y))
                                    Mock.a
                                    makeTruePredicate
                                ]
                            )
                        )
                    ]
                )
                (Mock.f (mkElemVar Mock.x))
        assertEqualWithExplanation "" expect actual

    , testCase "Falls back to evaluating the definition." $ do
        let expect =
                Conditional
                    { term = Mock.a
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        actual <-
            evaluate
                (Map.fromList
                    [   ( AxiomIdentifier.Application Mock.fId
                        , simplifierWithFallback
                            (axiomEvaluator
                                (Mock.f (Mock.g (mkElemVar Mock.x)))
                                Mock.b
                            )
                            (definitionEvaluation
                                [ axiom
                                    (Mock.f (mkElemVar Mock.y))
                                    Mock.a
                                    makeTruePredicate
                                ]
                            )
                        )
                    ]
                )
                (Mock.f (mkElemVar Mock.x))
        assertEqualWithExplanation "" expect actual

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
        assertEqualWithExplanation "" expect actual
    ]

test_Nat :: [TestTree]
test_Nat =
    [ matches "plus(0, N) matches plus(0, 1)"
        (plus zero varN)
        (plus zero one)
        [(ElemVar natN, one)]
    , doesn'tMatch "plus(succ(M), N) doesn't match plus(0, 1)"
        (plus (succ varM) varN)
        (plus zero one)
    , matches "plus(succ(M), N) matches plus(1, 1)"
        (plus (succ varM) varN)
        (plus one one)
        [(ElemVar natM, zero), (ElemVar natN, one)]
    , applies            "plus(0, N) => ... ~ plus (0, 1)"
        [plusZeroRule]
        (plus zero one)
    , notApplies         "plus(0, N) => ... ~ plus (1, 1)"
        [plusZeroRule]
        (plus one one)
    , notApplies         "plus(Succ(M), N) => ... ~ plus (0, 1)"
        [plusSuccRule]
        (plus zero one)
    , applies            "plus(Succ(M), N) => ... ~ plus (1, 1)"
        [plusSuccRule]
        (plus one one)
    , applies            "plus(0, 1) => ..."
        plusRules
        (plus zero one)
    , applies            "plus(1, 1) => ..."
        plusRules
        (plus one one)
    , equals "0 + 1 = 1 : Nat" (plus zero one) one
    , equals "0 + 1 = 1 : Nat" (plus one one) two
    , equals "0 * 1 = 0 : Nat" (times zero one) zero
    , equals "1 * 1 = 1 : Nat" (times one one) one
    , equals "1 * 2 = 2 : Nat" (times one two) two
    , equals "2 * 1 = 2 : Nat" (times two one) two
    , equals "0! = 1 : Nat" (factorial zero) one
    , equals "1! = 1 : Nat" (factorial one) one
    , equals "2! = 2 : Nat" (factorial two) two
    , equals "fibonacci(0) = 1 : Nat" (fibonacci zero) one
    , equals "fibonacci(1) = 1 : Nat" (fibonacci one) one
    , equals "fibonacci(2) = 2 : Nat" (fibonacci two) two
    ]
  where
    -- Evaluation tests: check the result of evaluating the term
    equals comment term expect =
        testCase comment $ do
            actual <- evaluate natSimplifiers term
            assertEqualWithExplanation "" (Pattern.fromTermLike expect) actual

-- Applied tests: check that one or more rules applies or not
withApplied
    :: (CommonAttemptedAxiom -> Assertion)
    -> TestName
    -> [EqualityRule Variable]
    -> TermLike Variable
    -> TestTree
withApplied check comment rules term =
    testCase comment $ do
        actual <- Axiom.evaluate (definitionEvaluation rules) term
        check actual

applies, notApplies
    :: TestName
    -> [EqualityRule Variable]
    -> TermLike Variable
    -> TestTree
applies =
    withApplied $ \attempted -> do
        results <- expectApplied attempted
        expectNoRemainders results
  where
    expectApplied NotApplicable     = assertFailure "Expected Applied"
    expectApplied (Applied results) = return results
    expectNoRemainders =
        assertBool "Expected no remainders"
        . isBottom
        . Lens.view (field @"remainders")
notApplies = withApplied (assertBool "Expected NotApplicable" . isNotApplicable)

natSort :: Sort
natSort =
    SortActualSort SortActual
        { sortActualName = testId "Nat"
        , sortActualSorts = []
        }

natM, natN :: ElementVariable Variable
natM = elemVarS "M" natSort
natN = elemVarS "N" natSort

varM, varN :: TermLike Variable
varM = mkElemVar natM
varN = mkElemVar natN

zeroSymbol, succSymbol :: Symbol
zeroSymbol = Mock.symbol "Zero" [] natSort & constructor & functional
succSymbol = Mock.symbol "Succ" [natSort] natSort & constructor & functional

plusSymbol, timesSymbol :: Symbol
plusSymbol = Mock.symbol "plus" [natSort, natSort] natSort & function
timesSymbol = Mock.symbol "times" [natSort, natSort] natSort & function

fibonacciSymbol, factorialSymbol :: Symbol
fibonacciSymbol = Mock.symbol "fibonacci" [natSort] natSort & function
factorialSymbol = Mock.symbol "factorial" [natSort] natSort & function

zero :: TermLike Variable
zero = mkApplySymbol zeroSymbol []

one, two :: TermLike Variable
one = succ zero
two = succ one

succ, fibonacci, factorial :: TermLike Variable -> TermLike Variable
succ n = mkApplySymbol succSymbol [n]
fibonacci n = mkApplySymbol fibonacciSymbol [n]
factorial n = mkApplySymbol factorialSymbol [n]

plus, times
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
plus n1 n2 = mkApplySymbol plusSymbol [n1, n2]
times n1 n2 = mkApplySymbol timesSymbol [n1, n2]

functionEvaluator
    :: Symbol
    -> [EqualityRule Variable]  -- ^ Function definition rules
    -> (AxiomIdentifier, BuiltinAndAxiomSimplifier)
functionEvaluator symb rules =
    (AxiomIdentifier.Application ident, definitionEvaluation rules)
  where
    ident = symbolConstructor symb

plusZeroRule, plusSuccRule :: EqualityRule Variable
plusZeroRule = axiom_ (plus zero varN) varN
plusSuccRule = axiom_ (plus (succ varM) varN) (succ (plus varM varN))


plusRules :: [EqualityRule Variable]
plusRules = [plusZeroRule, plusSuccRule]

plusEvaluator :: (AxiomIdentifier, BuiltinAndAxiomSimplifier)
plusEvaluator = functionEvaluator plusSymbol plusRules

timesEvaluator :: (AxiomIdentifier, BuiltinAndAxiomSimplifier)
timesEvaluator =
    functionEvaluator timesSymbol
        [ axiom_ (times zero varN) zero
        , axiom_ (times (succ varM) varN) (plus varN (times varM varN))
        ]

fibonacciEvaluator :: (AxiomIdentifier, BuiltinAndAxiomSimplifier)
fibonacciEvaluator =
    functionEvaluator fibonacciSymbol
        [ axiom_ (fibonacci zero) one
        , axiom_ (fibonacci one)  one
        , axiom_
            (fibonacci (succ (succ varN)))
            (plus (fibonacci (succ varN)) (fibonacci varN))
        ]

factorialEvaluator :: (AxiomIdentifier, BuiltinAndAxiomSimplifier)
factorialEvaluator =
    functionEvaluator factorialSymbol
        [ axiom_ (factorial zero)        (succ zero)
        , axiom_ (factorial (succ varN)) (times (succ varN) (factorial varN))
        ]

natSimplifiers :: BuiltinAndAxiomSimplifierMap
natSimplifiers =
    Map.fromList
        [ plusEvaluator
        , timesEvaluator
        , fibonacciEvaluator
        , factorialEvaluator
        ]

test_List :: [TestTree]
test_List =
    [ applies                  "lengthList([]) => ... ~ lengthList([])"
        [lengthListUnitRule]
        (lengthList unitList)
    , notApplies               "lengthList([]) => ... ~ lengthList(L)"
        [lengthListUnitRule]
        (lengthList varL)
    , notApplies               "lengthList([]) => ... !~ lengthList([1])"
        [lengthListUnitRule]
        (lengthList (mkList [mkInt 1]))
    , notApplies               "lengthList([]) => ... !~ lengthList([1, 2])"
        [lengthListUnitRule]
        (lengthList (mkList [mkInt 1, mkInt 2]))
    , notApplies               "lengthList(x : xs) => ... !~ lengthList([])"
        [lengthListConsRule]
        (lengthList unitList)
    , notApplies               "lengthList(x : xs) => ... !~ lengthList(L)"
        [lengthListConsRule]
        (lengthList varL)
    , applies                  "lengthList(x : xs) => ... ~ lengthList([1])"
        [lengthListConsRule]
        (lengthList (mkList [mkInt 1]))
    , applies                  "lengthList(x : xs) => ... ~ lengthList([1, 2])"
        [lengthListConsRule]
        (lengthList (mkList [mkInt 1, mkInt 2]))
    , applies                  "lengthList([]) => ..."
        lengthListRules
        (lengthList unitList)
    , applies                  "lengthList([1]) => ..."
        lengthListRules
        (lengthList (mkList [mkInt 1]))
    , applies                  "lengthList([12]) => ..."
        lengthListRules
        (lengthList (mkList [mkInt 1, mkInt 2]))
    , equals                   "lengthList([]) = 0 : Int"
        (lengthList (mkList []))
        (mkInt 0)
    , equals                   "lengthList([1]) = 1 : Int"
        (lengthList (mkList [mkInt 1]))
        (mkInt 1)
    , equals                   "lengthList([1, 2]) = 2 : Int"
        (lengthList (mkList [mkInt 1, mkInt 2]))
        (mkInt 2)

    , applies                  "removeList([], M) => ... ~ removeList([], [(0, 1)])"
        [removeListUnitRule]
        (removeList unitList (mkMap [(mkInt 0, mkInt 1)] []))
    , equals "removeList([1], [(0, 1)]) = [(0, 1)]"
        (removeList (mkList [mkInt 1]) (mkMap [(mkInt 0, mkInt 1)] []))
        (mkMap [(mkInt 0, mkInt 1)] [])
    ]
  where
    -- Evaluation tests: check the result of evaluating the term
    equals comment term expect =
        testCase comment $ do
            actual <- evaluate' listSimplifiers term
            assertEqualWithExplanation "" (Pattern.fromTermLike expect) actual

    evaluate'
        :: BuiltinAndAxiomSimplifierMap
        -> TermLike Variable
        -> IO (Pattern Variable)
    evaluate' functionIdToEvaluator patt =
        SMT.runSMT SMT.defaultConfig emptyLogger
        $ evalSimplifier env
        $ TermLike.simplify patt
      where
        env =
            Mock.env
                { metadataTools = Builtin.testMetadataTools
                , simplifierAxioms = functionIdToEvaluator
                }

listSort, intSort, mapSort :: Sort
listSort = Builtin.listSort
intSort = Builtin.intSort
mapSort = Builtin.mapSort

mkList :: [TermLike Variable] -> TermLike Variable
mkList = List.asInternal

mkInt :: Integer -> TermLike Variable
mkInt = Int.asInternal

mkMap
    :: [(TermLike Variable, TermLike Variable)]
    -> [TermLike Variable]
    -> TermLike Variable
mkMap elements opaques =
    Ac.asInternal Builtin.testMetadataTools Builtin.mapSort
    $ Map.normalizedMap elements opaques

removeMap :: TermLike Variable -> TermLike Variable -> TermLike Variable
removeMap = Builtin.removeMap

addInt :: TermLike Variable -> TermLike Variable -> TermLike Variable
addInt = Builtin.addInt

unitList :: TermLike Variable
unitList = mkList []

varX, varY, varL, mMap :: TermLike Variable
varX = mkElemVar (elemVarS (testId "xInt") intSort)
varY = mkElemVar (elemVarS (testId "yInt") intSort)
varL = mkElemVar (elemVarS (testId "lList") listSort)
mMap = mkElemVar (elemVarS (testId "mMap") mapSort)

lengthListSymbol :: Symbol
lengthListSymbol = Mock.symbol "lengthList" [listSort] intSort & function

lengthList :: TermLike Variable -> TermLike Variable
lengthList l = mkApplySymbol lengthListSymbol [l]

concatList :: TermLike Variable -> TermLike Variable -> TermLike Variable
concatList = Builtin.concatList

consList :: TermLike Variable -> TermLike Variable -> TermLike Variable
consList x xs = concatList (mkList [x]) xs

lengthListUnitRule, lengthListConsRule :: EqualityRule Variable
lengthListUnitRule = axiom_ (lengthList unitList) (mkInt 0)
lengthListConsRule =
    axiom_
        (lengthList (consList varX varL))
        (addInt (mkInt 1) (lengthList varL))

lengthListRules :: [EqualityRule Variable]
lengthListRules = [ lengthListUnitRule , lengthListConsRule ]

lengthListEvaluator :: (AxiomIdentifier, BuiltinAndAxiomSimplifier)
lengthListEvaluator = functionEvaluator lengthListSymbol lengthListRules

removeListSymbol :: Symbol
removeListSymbol =
    Mock.symbol "removeList" [listSort, mapSort] mapSort & function

removeList :: TermLike Variable -> TermLike Variable -> TermLike Variable
removeList l m = mkApplySymbol removeListSymbol [l, m]

removeListUnitRule, removeListConsRule :: EqualityRule Variable
removeListUnitRule = axiom_ (removeList unitList mMap) mMap
removeListConsRule =
    axiom_
        (removeList (consList varX varL) mMap)
        (removeMap mMap varX)

removeListRules :: [EqualityRule Variable]
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
        AxiomIdentifier.Application
        $ symbolConstructor Builtin.addIntSymbol
    Just removeMapEvaluator = Map.lookup "MAP.remove" Map.builtinFunctions
    removeMapId =
        AxiomIdentifier.Application
        $ symbolConstructor Builtin.removeMapSymbol

test_Map :: [TestTree]
test_Map =
    [ equals "lookupMap(.Map, 1) = lookupMap(.Map, 1)"
        (lookupMap (mkMap [] []) (mkInt 1))
        (lookupMap (mkMap [] []) (mkInt 1))
    , equals "lookupMap(1 |-> 2, 1) = 2"
        (lookupMap (mkMap [(mkInt 1, mkInt 2)] []) (mkInt 1))
        (mkInt 2)
    , equals "lookupMap(0 |-> 1  1 |-> 2, 1) = 2"
        (lookupMap (mkMap [(mkInt 0, mkInt 1), (mkInt 1, mkInt 2)] []) (mkInt 1))
        (mkInt 2)
    ]
  where
    -- Evaluation tests: check the result of evaluating the term
    equals
        :: HasCallStack
        => TestName
        -> TermLike Variable
        -> TermLike Variable
        -> TestTree
    equals comment term expect =
        testCase comment $ do
            actual <- evaluate' mapSimplifiers term
            assertEqualWithExplanation "" (Pattern.fromTermLike expect) actual

    evaluate'
        :: BuiltinAndAxiomSimplifierMap
        -> TermLike Variable
        -> IO (Pattern Variable)
    evaluate' functionIdToEvaluator patt =
        SMT.runSMT SMT.defaultConfig emptyLogger
        $ evalSimplifier env
        $ TermLike.simplify patt
      where
        env =
            Mock.env
                { metadataTools = Builtin.testMetadataTools
                , simplifierAxioms = functionIdToEvaluator
                }

lookupMapSymbol :: Symbol
lookupMapSymbol = Mock.symbol "lookupMap" [mapSort, intSort] intSort & function

lookupMap :: TermLike Variable -> TermLike Variable -> TermLike Variable
lookupMap m k = mkApplySymbol lookupMapSymbol [m, k]

lookupMapRule :: EqualityRule Variable
lookupMapRule = axiom_ (lookupMap (mkMap [(varX, varY)] [mMap]) varX) varY

lookupMapRules :: [EqualityRule Variable]
lookupMapRules = [lookupMapRule]

lookupMapEvaluator :: (AxiomIdentifier, BuiltinAndAxiomSimplifier)
lookupMapEvaluator = functionEvaluator lookupMapSymbol lookupMapRules

mapSimplifiers :: BuiltinAndAxiomSimplifierMap
mapSimplifiers =
    Map.fromList
        [ lookupMapEvaluator
        ]

test_Pair :: [TestTree]
test_Pair =
    [ applies "pair constructor axiom applies"
        [pairCtorAxiom]
        (mkExists xInt . mkExists yInt $ mkPair (mkElemVar xInt) (mkElemVar yInt))
    ]

mkPair :: TermLike Variable -> TermLike Variable -> TermLike Variable
mkPair = Builtin.pair

xInt, yInt :: ElementVariable Variable
xInt = elemVarS (testId "xInt") intSort
yInt = elemVarS (testId "yInt") intSort

pairCtorAxiom :: EqualityRule Variable
pairCtorAxiom =
    EqualityRule $ rulePattern
        (mkExists xInt . mkExists yInt $ mkPair (mkElemVar xInt) (mkElemVar yInt))
        (mkTop $ Builtin.pairSort intSort intSort)

axiomEvaluator
    :: TermLike Variable
    -> TermLike Variable
    -> BuiltinAndAxiomSimplifier
axiomEvaluator left right =
    BuiltinAndAxiomSimplifier
        (equalityRuleEvaluator (axiom left right makeTruePredicate))

axiom
    :: TermLike Variable
    -> TermLike Variable
    -> Syntax.Predicate Variable
    -> EqualityRule Variable
axiom left right predicate =
    EqualityRule (RulePattern.rulePattern left right) { requires = predicate }

axiom_
    :: TermLike Variable
    -> TermLike Variable
    -> EqualityRule Variable
axiom_ left right = axiom left right makeTruePredicate

appliedMockEvaluator
    :: Pattern Variable -> BuiltinAndAxiomSimplifier
appliedMockEvaluator result =
    BuiltinAndAxiomSimplifier
    $ mockEvaluator
    $ AttemptedAxiom.Applied AttemptedAxiomResults
        { results = OrPattern.fromPatterns
            [Test.Kore.Step.Function.Integration.mapVariables result]
        , remainders = OrPattern.fromPatterns []
        }

mapVariables
    ::  ( FreshVariable variable
        , SortedVariable variable
        )
    => Pattern Variable
    -> Pattern variable
mapVariables =
    Pattern.mapVariables $ \v ->
        fromVariable v { variableCounter = Just (Element 1) }

mockEvaluator
    :: Monad simplifier
    => AttemptedAxiom variable
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -> TermLike variable
    -> simplifier (AttemptedAxiom variable)
mockEvaluator evaluation _ _ _ _ = return evaluation

evaluate
    :: BuiltinAndAxiomSimplifierMap
    -> TermLike Variable
    -> IO (Pattern Variable)
evaluate functionIdToEvaluator patt =
    SMT.runSMT SMT.defaultConfig emptyLogger
    $ evalSimplifier Mock.env { simplifierAxioms = functionIdToEvaluator }
    $ TermLike.simplify patt
