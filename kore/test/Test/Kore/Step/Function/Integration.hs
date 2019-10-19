module Test.Kore.Step.Function.Integration
    ( test_functionIntegration
    , test_Nat
    , test_List
    , test_lookupMap
    , test_updateMap
    ) where

import Test.Tasty

import qualified Control.Lens as Lens
import Data.Function
import Data.Generics.Product
import Data.Map
    ( Map
    )
import qualified Data.Map as Map
import Data.Maybe
import Data.Proxy
import qualified Data.Text.Prettyprint.Doc as Pretty
import Prelude hiding
    ( succ
    )

import Data.Sup
import Kore.ASTVerifier.DefinitionVerifier
import Kore.ASTVerifier.Error
    ( VerifyError
    )
import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin as Builtin
import qualified Kore.Builtin.AssociativeCommutative as Ac
import qualified Kore.Builtin.Int as Int
    ( builtinFunctions
    )
import qualified Kore.Builtin.Map as Map
    ( builtinFunctions
    )
import qualified Kore.Error
import Kore.IndexedModule.IndexedModule as IndexedModule
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    )
import qualified Kore.IndexedModule.MetadataToolsBuilder as MetadataTools
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.Symbol
import Kore.Internal.TermLike
import Kore.Predicate.Predicate
    ( makeAndPredicate
    , makeCeilPredicate
    , makeEqualsPredicate
    , makeTruePredicate
    )
import qualified Kore.Predicate.Predicate as Syntax
    ( Predicate
    )
import Kore.Step.Axiom.EvaluationStrategy
    ( builtinEvaluation
    , definitionEvaluation
    , firstFullEvaluation
    , simplificationEvaluation
    , simplifierWithFallback
    )
import Kore.Step.Axiom.Identifier
    ( AxiomIdentifier
    )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
import qualified Kore.Step.Function.Memo as Memo
import Kore.Step.Rule
    ( EqualityRule (..)
    )
import Kore.Step.Rule as RulePattern
    ( RulePattern (..)
    , rulePattern
    )
import qualified Kore.Step.Simplification.Predicate as Simplifier.Predicate
import qualified Kore.Step.Simplification.Simplifier as Simplifier
import Kore.Step.Simplification.Simplify
import Kore.Step.Simplification.Simplify as AttemptedAxiom
    ( AttemptedAxiom (..)
    )
import qualified Kore.Step.Simplification.TermLike as TermLike
import Kore.Syntax.Definition hiding
    ( Symbol (..)
    )
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unparser
import Kore.Variables.Fresh
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import Test.Kore
import qualified Test.Kore.Builtin.Bool as Bool
import qualified Test.Kore.Builtin.Builtin as Builtin
import qualified Test.Kore.Builtin.Definition as Builtin
import qualified Test.Kore.Builtin.Int as Int
import qualified Test.Kore.Builtin.List as List
import qualified Test.Kore.Builtin.Map as Map
import Test.Kore.Step.Axiom.Matcher
    ( doesn'tMatch
    , matches
    )
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext

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
        assertEqual "" expect actual

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
        assertEqual "" expect actual

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
        assertEqual "" expect actual

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
        assertEqual "" expect actual

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
        assertEqual "" expect actual

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
        assertEqual "" expect actual

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
        assertEqual "" expect actual

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
        assertEqual "" expect actual

    , testCase "Merges conditions" $ do
        let expect =
                Conditional
                    { term = Mock.functional11 (Mock.functional20 Mock.e Mock.e)
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate Mock.cf)
                            (makeCeilPredicate Mock.cg)
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
        assertEqual "" expect actual

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
        assertEqual "" expect actual

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
        assertEqual "" expect actual

    , testCase "Simplifies substitution-predicate." $ do
        -- Mock.plain10 below prevents:
        -- 1. unification without substitution.
        -- 2. Transforming the 'and' in an equals predicate,
        --    as it would happen for functions.
        let expect =
                Conditional
                    { term = Mock.a
                    , predicate = makeCeilPredicate (Mock.plain10 Mock.cf)
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
        let message =
                (show . Pretty.vsep)
                    [ "Expected:"
                    , Pretty.indent 4 (unparse expect)
                    , "but found:"
                    , Pretty.indent 4 (unparse actual)
                    ]
        assertEqual message expect actual

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
        assertEqual "" expect actual

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
        assertEqual "" expect actual

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
        assertEqual "" expect actual

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
        assertEqual "" expect actual
    ]
  where
    evaluate
        :: BuiltinAndAxiomSimplifierMap
        -> TermLike Variable
        -> IO (Pattern Variable)
    evaluate functionIdToEvaluator patt =
        runSimplifier Mock.env { simplifierAxioms = functionIdToEvaluator }
        $ TermLike.simplify patt Predicate.top

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

-- Evaluation tests: check the result of evaluating the term
equals
    :: HasCallStack
    => TestName
    -> TermLike Variable
    -> [TermLike Variable]
    -> TestTree
equals comment term results =
    testCase comment $ do
        actual <- simplify term
        let expect = OrPattern.fromPatterns $ Pattern.fromTermLike <$> results
        assertEqual "" expect actual

simplify :: TermLike Variable -> IO (OrPattern Variable)
simplify =
    runSimplifier testEnv
    . (TermLike.simplifyToOr Predicate.top)

evaluateWith
    :: BuiltinAndAxiomSimplifier
    -> TermLike Variable
    -> IO CommonAttemptedAxiom
evaluateWith simplifier patt =
    runSimplifier testEnv
    $ runBuiltinAndAxiomSimplifier simplifier Predicate.top patt

-- Applied tests: check that one or more rules applies or not
withApplied
    :: (CommonAttemptedAxiom -> Assertion)
    -> TestName
    -> [EqualityRule Variable]
    -> TermLike Variable
    -> TestTree
withApplied check comment rules term =
    testCase comment $ do
        actual <- evaluateWith (definitionEvaluation rules) term
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

functionSimplifier
    :: Symbol
    -> [EqualityRule Variable]  -- ^ Function simplification rule
    -> (AxiomIdentifier, BuiltinAndAxiomSimplifier)
functionSimplifier symb rules =
    ( AxiomIdentifier.Application ident
    , firstFullEvaluation (simplificationEvaluation <$> rules)
    )
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
        [mkInt 0]
    , equals                   "lengthList([1]) = 1 : Int"
        (lengthList (mkList [mkInt 1]))
        [mkInt 1]
    , equals                   "lengthList([1, 2]) = 2 : Int"
        (lengthList (mkList [mkInt 1, mkInt 2]))
        [mkInt 2]

    , applies                  "removeList([], M) => ... ~ removeList([], [(0, 1)])"
        [removeListUnitRule]
        (removeList unitList (mkMap [(mkInt 0, mkInt 1)] []))
    , equals "removeList([1], [(0, 1)]) = [(0, 1)]"
        (removeList (mkList [mkInt 1]) (mkMap [(mkInt 0, mkInt 1)] []))
        [mkMap [(mkInt 0, mkInt 1)] []]
    ]

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

varX, varY, varL, mMapTerm :: TermLike Variable
varX = mkElemVar xInt
varY = mkElemVar yInt
varL = mkElemVar (elemVarS (testId "lList") listSort)
mMapTerm = mkElemVar mMap

mMap :: ElementVariable Variable
mMap = elemVarS (testId "mMap") mapSort

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
removeListUnitRule = axiom_ (removeList unitList mMapTerm) mMapTerm
removeListConsRule =
    axiom_
        (removeList (consList varX varL) mMapTerm)
        (removeMap mMapTerm varX)

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

test_lookupMap :: [TestTree]
test_lookupMap =
    [ equals "lookupMap(.Map, 1) = \\bottom"
        (lookupMap (mkMap [] []) (mkInt 1))
        []
    , equals "lookupMap(1 |-> 2, 1) = 2"
        (lookupMap (mkMap [(mkInt 1, mkInt 2)] []) (mkInt 1))
        [mkInt 2]
    , equals "lookupMap(0 |-> 1  1 |-> 2, 1) = 2"
        (lookupMap (mkMap [(mkInt 0, mkInt 1), (mkInt 1, mkInt 2)] []) (mkInt 1))
        [mkInt 2]
    ]

lookupMapSymbol :: Symbol
lookupMapSymbol = Builtin.lookupMapSymbol

lookupMap :: TermLike Variable -> TermLike Variable -> TermLike Variable
lookupMap = Builtin.lookupMap

lookupMapRule :: EqualityRule Variable
lookupMapRule = axiom_ (lookupMap (mkMap [(varX, varY)] [mMapTerm]) varX) varY

lookupMapRules :: [EqualityRule Variable]
lookupMapRules = [lookupMapRule]

lookupMapEvaluator :: (AxiomIdentifier, BuiltinAndAxiomSimplifier)
lookupMapEvaluator = functionEvaluator lookupMapSymbol lookupMapRules

test_updateMap :: [TestTree]
test_updateMap =
    [ notApplies "different concrete keys"
        [updateMapSimplifier]
        (updateMap
            (updateMap mMapTerm (mkInt 0) (mkInt 1))
            (mkInt 1)
            (mkInt 2)
        )
    , applies "same concrete key"
        [updateMapSimplifier]
        (updateMap
            (updateMap mMapTerm (mkInt 0) (mkInt 1))
            (mkInt 0)
            (mkInt 2)
        )
    , notApplies "different abstract keys; evaluates requires with SMT"
        [updateMapSimplifier]
        (updateMap
            (updateMap mMapTerm (mkElemVar xInt) (mkInt 1))
            (addInt (mkElemVar xInt) (mkInt 1))
            (mkInt 2)
        )
    , notApplies "different keys; evaluates requires with function rule"
        [updateMapSimplifier]
        (updateMap
            (updateMap Builtin.unitMap (mkInt 0) (mkInt 1))
            (addInt (mkInt 0) (Builtin.dummyInt (mkInt 1)))
            (mkInt 2)
        )
    , equals "different keys; evaluates updateMap"
        (updateMap
            (updateMap Builtin.unitMap (mkInt 0) (mkInt 1))
            (addInt (mkInt 0) (Builtin.dummyInt (mkInt 1)))
            (mkInt 2)
        )
        [mkMap [(mkInt 0, mkInt 1), (mkInt 1, mkInt 2)] []]
    , applies "same abstract key"
        [updateMapSimplifier]
        (updateMap
            (updateMap mMapTerm (mkElemVar xInt) (mkInt 1))
            (mkElemVar xInt)
            (mkInt 2)
        )
    ]

updateMap
    :: TermLike Variable  -- ^ Map
    -> TermLike Variable  -- ^ Key
    -> TermLike Variable  -- ^ Value
    -> TermLike Variable
updateMap = Builtin.updateMap

updateMapSimplifier :: EqualityRule Variable
updateMapSimplifier =
    axiom
        (updateMap (updateMap mMapTerm u v) x y)
        (updateMap mMapTerm u y)
        (makeEqualsPredicate (Builtin.keqBool (injK u) (injK x)) (mkBool True))
  where
    [u, v, x, y] = mkElemVar <$> [uInt, vInt, xInt, yInt]
    injK = Builtin.inj Builtin.kSort

dummyIntSimplifier :: EqualityRule Variable
dummyIntSimplifier =
    axiom_ (Builtin.dummyInt (mkElemVar xInt)) (mkElemVar xInt)

mkBool :: Bool -> TermLike Variable
mkBool = Bool.asInternal

mapSimplifiers :: BuiltinAndAxiomSimplifierMap
mapSimplifiers =
    Map.fromList
        [ lookupMapEvaluator
        , functionSimplifier Builtin.updateMapSymbol [updateMapSimplifier]
        , functionEvaluator Builtin.dummyIntSymbol [dummyIntSimplifier]
        ]

uInt, vInt, xInt, yInt :: ElementVariable Variable
uInt = elemVarS (testId "uInt") intSort
vInt = elemVarS (testId "vInt") intSort
xInt = elemVarS (testId "xInt") intSort
yInt = elemVarS (testId "yInt") intSort

axiomEvaluator
    :: TermLike Variable
    -> TermLike Variable
    -> BuiltinAndAxiomSimplifier
axiomEvaluator left right =
    simplificationEvaluation (axiom left right makeTruePredicate)

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
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -> TermLike variable
    -> Predicate variable
    -> simplifier (AttemptedAxiom variable)
mockEvaluator evaluation _ _ _ _ = return evaluation

-- ---------------------------------------------------------------------
-- * Definition

natModuleName :: ModuleName
natModuleName = ModuleName "NAT"

natSortDecl :: Sentence pattern'
natSortDecl =
    asSentence SentenceSort
        { sentenceSortName =
            let SortActualSort SortActual { sortActualName } = natSort
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
            ]
        }

testDefinition :: ParsedDefinition
testDefinition =
    Builtin.testDefinition
    & field @"definitionModules" Lens.<>~ [natModule, testModule]

verify
    :: ParsedDefinition
    -> Either
        (Kore.Error.Error VerifyError)
        (Map
            ModuleName (VerifiedModule Attribute.Symbol Attribute.Axiom)
        )
verify = verifyAndIndexDefinition attrVerify Builtin.koreVerifiers
  where
    attrVerify = defaultAttributesVerification Proxy Proxy

verifiedModules
    :: Map ModuleName (VerifiedModule Attribute.Symbol Attribute.Axiom)
verifiedModules = Kore.Error.assertRight (verify testDefinition)

verifiedModule :: VerifiedModule Attribute.Symbol Attribute.Axiom
Just verifiedModule = Map.lookup testModuleName verifiedModules

testMetadataTools :: SmtMetadataTools Attribute.Symbol
testMetadataTools = MetadataTools.build verifiedModule

testSubstitutionSimplifier
    :: MonadSimplify simplifier => PredicateSimplifier simplifier
testSubstitutionSimplifier = Simplifier.Predicate.create

testEvaluators :: BuiltinAndAxiomSimplifierMap
testEvaluators = Builtin.koreEvaluators verifiedModule

testTermLikeSimplifier :: TermLikeSimplifier
testTermLikeSimplifier = Simplifier.create

testEnv :: Env Simplifier
testEnv =
    Env
        { metadataTools = testMetadataTools
        , simplifierTermLike = testTermLikeSimplifier
        , simplifierPredicate = testSubstitutionSimplifier
        , simplifierAxioms =
            mconcat
                [ testEvaluators
                , natSimplifiers
                , listSimplifiers
                , mapSimplifiers
                ]
        , memo = Memo.forgetful
        }
