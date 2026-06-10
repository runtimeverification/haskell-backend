{-# LANGUAGE QuasiQuotes #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use ++" #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Test.Booster.Pattern.ApplyEquations (
    test_evaluateFunction,
    test_simplify,
    test_simplifyPattern,
    test_simplifyConstraint,
    test_llvmCacheUsedForConstraints,
    test_equationCacheTaint,
    test_argumentIndexing,
    test_localFixpoint,
    test_ruleMetrics,
    test_errors,
) where

import Control.Exception (finally)
import Control.Monad (void)
import Control.Monad.Logger (runNoLoggingT)
import Data.ByteString (ByteString)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Test.Tasty
import Test.Tasty.HUnit

import Booster.Definition.Attributes.Base
import Booster.Definition.Base
import Booster.GlobalState (
    EquationOptions (..),
    readGlobalEquationOptions,
    writeGlobalEquationOptions,
 )
import Booster.Metrics (RuleMetrics (..), flushRuleMetrics)
import Booster.Pattern.ApplyEquations
import Booster.Pattern.Base
import Booster.Pattern.Bool
import Booster.Pattern.Index (CellIndex (..), TermIndex (..))
import Booster.Pattern.Util (sortOfTerm)
import Booster.SMT.Interface (noSolver)
import Booster.Syntax.Json.Internalise (trm)
import Booster.Util (Flag (..))
import Test.Booster.Fixture hiding (inj)
import Test.Booster.Util ((@?>>=))

inj :: Symbol
inj = injectionSymbol

test_evaluateFunction :: TestTree
test_evaluateFunction =
    testGroup
        "Evaluating functions using rules without side conditions"
        [ -- f1(a) => a
          testCase "Simple function evaluation" $ do
            eval TopDown [trm| f1{}(con2{}(A:SomeSort{})) |] @?>>= Right [trm| con2{}(A:SomeSort{}) |]
            eval BottomUp [trm| f1{}(con2{}(A:SomeSort{})) |] @?>>= Right [trm| con2{}(A:SomeSort{}) |]
        , -- f2(f1(f1(con2(a)))) => f2(con2(a)). f2 is marked as partial, so not evaluating
          testCase "Nested function applications, one not to be evaluated" $ do
            let subj = [trm| f2{}(f1{}(f1{}(con2{}(A:SomeSort{})))) |]
                goal = [trm| f2{}(con2{}(A:SomeSort{})) |]
            eval TopDown subj @?>>= Right goal
            eval BottomUp subj @?>>= Right goal
        , -- f1(f2(f1(con2(a)))) => f1(f2(con2(a))). Again f2 partial, so not evaluating,
          -- therefore f1(x) => x not applied to unevaluated value
          testCase "Nested function applications with partial function inside" $ do
            let subj = [trm| f1{}(f2{}(f1{}(con2{}(A:SomeSort{})))) |]
                goal = [trm| f1{}(f2{}(con2{}(A:SomeSort{}))) |]
            eval TopDown subj @?>>= Right goal
            eval BottomUp subj @?>>= Right goal
        , -- f1(con1(con1(..con1(con2(a))..))) => con2(con2(..con2(a)..))
          -- using f1(con1(X)) => con2(X) repeatedly
          testCase "Recursive evaluation" $ do
            let subj depth = app f1 [iterate (apply con1) a !! depth]
                a = app con2 [var "A" someSort]
                apply f = app f . (: [])
                n `times` f = foldr (.) id (replicate n $ apply f)
            -- top-down evaluation: a single iteration is enough
            eval TopDown (subj 101) @?>>= Right (101 `times` con2 $ a)
            -- bottom-up evaluation: `depth` many iterations
            eval BottomUp (subj 100) @?>>= Right (100 `times` con2 $ a)
            isTooManyIterations =<< eval BottomUp (subj 101)
        , -- con3(f1(con2(a)), f1(con1(con2(b)))) => con3(con2(a), con2(con2(b)))
          testCase "Several function calls inside a constructor" $ do
            eval TopDown [trm| con3{}(f1{}(con2{}(A:SomeSort{})), f1{}(con1{}(con2{}(B:SomeSort{})))) |]
                @?>>= Right [trm| con3{}(con2{}(A:SomeSort{}), con2{}(con2{}(B:SomeSort{}))) |]
        , -- f1(inj{sub,some}(con4(a, b))) => f1(a) => a (not using f1-is-identity)
          testCase "Matching uses priorities" $ do
            eval TopDown [trm| f1{}(inj{AnotherSort{}, SomeSort{}}(con4{}(A:SomeSort{}, B:SomeSort{}))) |]
                @?>>= Right [trm| A:SomeSort{} |]
        , -- f1(con1("hey")) unmodified, since "hey" is concrete
          testCase "f1 with concrete argument, constraints prevent rule application" $ do
            let subj = [trm| f1{}(con1{}( \dv{SomeSort{}}("hey")) ) |]
            eval TopDown subj @?>>= Right subj
            eval BottomUp subj @?>>= Right subj
        , testCase "f2 with symbolic argument, constraint prevents rule application" $ do
            let subj = [trm| f2{}(con1{}(A:SomeSort{})) |]
            eval TopDown subj @?>>= Right subj
            eval BottomUp subj @?>>= Right subj
        , testCase "f2 with concrete argument, satisfying constraint" $ do
            let subj = [trm| f2{}(con1{}(\dv{SomeSort{}}("hey"))) |]
                result = [trm| f2{}(\dv{SomeSort{}}("hey")) |]
            eval TopDown subj @?>>= Right result
            eval BottomUp subj @?>>= Right result
        ]
  where
    eval direction t = do
        ns <- noSolver
        runNoLoggingT $ fst <$> evaluateTerm direction funDef Nothing ns mempty mempty t

    isTooManyIterations (Left (TooManyIterations _n _ _)) = pure ()
    isTooManyIterations (Left err) = assertFailure $ "Unexpected error " <> show err
    isTooManyIterations (Right r) = assertFailure $ "Unexpected result" <> show r

test_simplify :: TestTree
test_simplify =
    testGroup
        "Performing simplifications"
        [ testCase "No simplification applies" $ do
            let subj = [trm| f1{}(f2{}(A:SomeSort{})) |]
            simpl TopDown subj @?>>= Right subj
            simpl BottomUp subj @?>>= Right subj
        , -- con1(con2(f2(a))) => con2(f2(a))
          testCase "Simplification of constructors" $ do
            let subj = app con1 [app con2 [app f2 [a]]]
            simpl TopDown subj @?>>= Right (app con2 [app f2 [a]])
            simpl BottomUp subj @?>>= Right (app con2 [app f2 [a]])
        , -- con3(f2(a), f2(a)) => inj{sub,some}(con4(f2(a), f2(a)))
          testCase "Simplification with argument match" $ do
            let subj = [trm| con3{}(f2{}(A:SomeSort{}), f2{}(A:SomeSort{})) |]
                result = [trm| inj{AnotherSort{}, SomeSort{}}(con4{}(f2{}(A:SomeSort{}), f2{}(A:SomeSort{}))) |]
            simpl TopDown subj @?>>= Right result
            simpl BottomUp subj @?>>= Right result
        ]
  where
    simpl direction t = do
        ns <- noSolver
        runNoLoggingT $ fst <$> evaluateTerm direction simplDef Nothing ns mempty mempty t
    a = var "A" someSort

test_simplifyPattern :: TestTree
test_simplifyPattern =
    testGroup
        "Performing Pattern simplifications"
        [ testCase "No simplification applies" $ do
            let subj = [trm| f1{}(f2{}(A:SomeSort{})) |]
            simpl (Pattern_ subj) @?>>= Right (Pattern_ subj)
            simpl (Pattern_ subj) @?>>= Right (Pattern_ subj)
        , -- con1(con2(f2(a))) => con2(f2(a))
          testCase "Simplification of constructors" $ do
            let subj = app con1 [app con2 [app f2 [a]]]
            simpl (Pattern_ subj)
                @?>>= Right (Pattern_ $ app con2 [app f2 [a]])
            simpl (Pattern_ subj)
                @?>>= Right (Pattern_ $ app con2 [app f2 [a]])
        , -- con3(f2(a), f2(a)) => inj{sub,some}(con4(f2(a), f2(a)))
          testCase "Simplification with argument match" $ do
            let subj = Pattern_ [trm| con3{}(f2{}(A:SomeSort{}), f2{}(A:SomeSort{})) |]
                result =
                    Pattern_ [trm| inj{AnotherSort{}, SomeSort{}}(con4{}(f2{}(A:SomeSort{}), f2{}(A:SomeSort{}))) |]
            simpl subj @?>>= Right result
        ]
  where
    simpl t = do
        ns <- noSolver
        runNoLoggingT $ fst <$> evaluatePattern simplDef Nothing ns mempty t
    a = var "A" someSort

test_simplifyConstraint :: TestTree
test_simplifyConstraint =
    testGroup
        "Performing Predicate simplifications"
        [ testGroup
            "==K simplification"
            $ concat
                [ testCaseEqualsK
                    "Same constructor, same variable"
                    [trm| con1{}(A:SomeSort{}) |]
                    [trm| con1{}(A:SomeSort{}) |]
                    (const TrueBool)
                    (const TrueBool)
                , testCaseEqualsK
                    "Same constructor, different variables"
                    [trm| con1{}(A:SomeSort{}) |]
                    [trm| con1{}(B:SomeSort{}) |]
                    id
                    id
                , testCaseEqualsK
                    "Different constructors, same variable"
                    [trm| con1{}(A:SomeSort{}) |]
                    [trm| con2{}(A:SomeSort{}) |]
                    (const FalseBool)
                    (const FalseBool)
                , testCaseEqualsK
                    "Constructor with domain value"
                    [trm| con1{}(A:SomeSort{}) |]
                    [trm| \dv{SomeSort{}}("hey") |]
                    (const FalseBool)
                    (const FalseBool)
                , testCaseEqualsK
                    "Function with map, indeterminate"
                    [trm| f3{}(A:SomeSort{}) |]
                    (KMap testKMapDefinition [] Nothing)
                    id
                    id
                , testCaseEqualsK
                    "Constructor with function, indeterminate"
                    [trm| con1{}(B:SomeSort{}) |]
                    [trm| f2{}(A:SomeSort{}) |]
                    id
                    id
                , testCaseEqualsK
                    "Constructor with variable, indeterminate"
                    [trm| con1{}(B:SomeSort{}) |]
                    [trm| A:SomeSort{} |]
                    id
                    id
                ]
        ]
  where
    testCaseEqualsK name lhs rhs exp1 exp2 =
        [ testCase name $
            let subj =
                    EqualsK (KSeq (sortOfTerm lhs) lhs) (KSeq (sortOfTerm rhs) rhs)
             in simpl (Predicate subj) @?>>= Right (Predicate (exp1 subj))
        , testCase (name <> " (flipped)") $
            let subj =
                    EqualsK (KSeq (sortOfTerm rhs) rhs) (KSeq (sortOfTerm lhs) lhs)
             in simpl (Predicate subj) @?>>= Right (Predicate (exp2 subj))
        ]

    simpl t =
        do
            ns <- noSolver
            runNoLoggingT $ fst <$> simplifyConstraint testDefinition Nothing ns mempty mempty t

test_llvmCacheUsedForConstraints :: TestTree
test_llvmCacheUsedForConstraints =
    testGroup
        "LLVM cache is consulted when simplifying concrete constraints"
        [ testCase "Without a cache entry, the term is evaluated" $
            -- the KEQUAL.eq hook evaluates the trivial equation to true
            simpl mempty (Predicate concreteEqualsK) @?>>= Right (Predicate TrueBool)
        , testCase "A cache entry short-circuits evaluation" $ do
            -- seeded with a (deliberately wrong) cached result that
            -- evaluation could never produce, proving the lookup
            -- happens before any evaluation of the term
            let seeded = mempty{llvm = Map.singleton concreteEqualsK FalseBool}
            simpl seeded (Predicate concreteEqualsK) @?>>= Right (Predicate FalseBool)
        ]
  where
    -- concrete (ground) term, evaluates to TrueBool via the ==K hook
    concreteEqualsK =
        let t = [trm| con1{}(\dv{SomeSort{}}("hey")) |]
         in EqualsK (KSeq (sortOfTerm t) t) (KSeq (sortOfTerm t) t)

    simpl cache t = do
        ns <- noSolver
        runNoLoggingT $ fst <$> simplifyConstraint testDefinition Nothing ns cache mempty t

{- | Smoke test for the depth-1 candidate filter: skipping is
behaviour-preserving by construction (simplifications skip only
cannot-succeed pairs, function equations only decisive failures), so
results must be identical with the flag on.
-}
test_argumentIndexing :: TestTree
test_argumentIndexing =
    testCase "Evaluation results are unchanged with argument indexing enabled" $ do
        defaults <- readGlobalEquationOptions
        writeGlobalEquationOptions defaults{argumentIndexing = True}
        runChecks `finally` writeGlobalEquationOptions defaults
  where
    runChecks = do
        -- function equations: the f1(con1(X)) rule is filtered for a
        -- con2 argument, the identity rule still applies
        evalWith funDef [trm| f1{}(con2{}(A:SomeSort{})) |]
            >>= (@?= Right [trm| con2{}(A:SomeSort{}) |])
        -- concreteness-blocked rules behave as before (both rules are
        -- index-compatible, rejection happens after the match)
        evalWith funDef [trm| f1{}(con1{}(\dv{SomeSort{}}("hey"))) |]
            >>= (@?= Right [trm| f1{}(con1{}(\dv{SomeSort{}}("hey"))) |])
        -- simplifications: priority order among surviving candidates is kept
        evalWith simplDef (app con1 [app con2 [app f2 [var "A" someSort]]])
            >>= (@?= Right (app con2 [app f2 [var "A" someSort]]))
        -- bare-variable argument: all con2-shaped rules are filtered
        -- via IdxVar, term is unchanged (as it would be via match
        -- failures without the filter)
        evalWith simplDef [trm| con1{}(X:SomeSort{}) |]
            >>= (@?= Right [trm| con1{}(X:SomeSort{}) |])

    evalWith def t = do
        ns <- noSolver
        runNoLoggingT $ fst <$> evaluateTerm BottomUp def Nothing ns mempty mempty t

test_localFixpoint :: TestTree
test_localFixpoint =
    -- must run after the iteration-limit test ("Recursive evaluation"),
    -- whose outcome the temporary flag window below would change if the
    -- two ran concurrently (the test binary runs tests in parallel)
    after AllFinish "Recursive evaluation" $
        testCase "Local fixpoint mode normalizes causal chains in one pass" $ do
            defaults <- readGlobalEquationOptions
            writeGlobalEquationOptions defaults{localFixpoint = True}
            runChecks `finally` writeGlobalEquationOptions defaults
  where
    runChecks = do
        -- standard scenarios give identical results
        evalWith funDef [trm| f1{}(con2{}(A:SomeSort{})) |]
            >>= (@?= Right [trm| con2{}(A:SomeSort{}) |])
        evalWith simplDef (app con1 [app con2 [app f2 [a]]])
            >>= (@?= Right (app con2 [app f2 [a]]))
        -- a causal chain of depth 101 exceeds the global-pass limit
        -- without local fixpoints (one whole-term pass per chain
        -- step, see "Recursive evaluation"), but normalizes in a
        -- single pass here
        let subj depth = app f1 [iterate (apply con1) start !! depth]
            start = app con2 [a]
            n `times` f = foldr (.) id (replicate n $ apply f)
        evalWith funDef (subj 101) >>= (@?= Right (101 `times` con2 $ start))
        -- node-level oscillation is detected per local step
        isLoop =<< evalWith loopDef (app f1 [app con1 [a]])

    a = var "A" someSort
    apply f = app f . (: [])

    isLoop (Left (EquationLoop _)) = pure ()
    isLoop other = assertFailure $ "Expected an equation loop, got " <> show other

    evalWith def t = do
        ns <- noSolver
        runNoLoggingT $ fst <$> evaluateTerm BottomUp def Nothing ns mempty mempty t

test_ruleMetrics :: TestTree
test_ruleMetrics =
    testCase "Equation attempts are recorded in the rule metrics accumulator" $ do
        -- the accumulator is process-global and tests run in
        -- parallel, so assertions are lower bounds on the fixture
        -- rules' shared mock unique id
        void flushRuleMetrics
        ns <- noSolver
        void . runNoLoggingT $
            evaluateTerm BottomUp funDef Nothing ns mempty mempty [trm| f1{}(con2{}(A:SomeSort{})) |]
        metrics <- flushRuleMetrics
        case Map.lookup mockUniqueId metrics of
            Nothing -> assertFailure "no metrics recorded for the fixture rule"
            Just m -> do
                assertBool "at least one attempt" $ m.attempts >= 1
                assertBool "at least one success" $ m.successes >= 1
                assertBool "non-zero total time" $ m.totalNs > 0
test_equationCacheTaint :: TestTree
test_equationCacheTaint =
    testGroup
        "Pure/tainted equation cache routing and retention"
        [ testCase "Unconditional equation result is cached as pure" $ do
            (res, cache) <- evalWithCache funDef mempty subj
            res @?= Right result
            Map.lookup subj cache.pureEquations @?= Just result
            cache.equations @?= mempty
        , testCase "Result of a rule with requires is cached as tainted" $ do
            (res, cache) <- evalWithCache requiresDef mempty subj
            res @?= Right result
            Map.lookup subj cache.equations @?= Just result
            Map.lookup subj cache.pureEquations @?= Nothing
        , testCase "Pure entries are consulted during evaluation" $ do
            -- seeded with a (deliberately wrong) result that evaluation
            -- could never produce, proving the entry short-circuits it
            let seeded = mempty{pureEquations = Map.singleton subj marker}
            (res, _) <- evalWithCache funDef seeded subj
            res @?= Right marker
        , testCase "Tainted entries are consulted during evaluation" $ do
            let seeded = mempty{equations = Map.singleton subj marker}
            (res, _) <- evalWithCache funDef seeded subj
            res @?= Right marker
        , testCase "New path condition wipes tainted entries but keeps pure ones" $ do
            -- markers under keys unrelated to the evaluated term, to
            -- observe what survives the ensures-triggered cache reset
            let pureMarkerKey = [trm| f1{}(con1{}(B:SomeSort{})) |]
                taintedMarkerKey = [trm| f2{}(con1{}(B:SomeSort{})) |]
                seeded =
                    mempty
                        { equations = Map.singleton taintedMarkerKey marker
                        , pureEquations = Map.singleton pureMarkerKey marker
                        }
            (res, cache) <- evalWithCache ensuresDef seeded subj
            res @?= Right result
            Map.lookup pureMarkerKey cache.pureEquations @?= Just marker
            Map.lookup taintedMarkerKey cache.equations @?= Nothing
            -- the rule had an ensures clause, so its own result is tainted
            Map.lookup subj cache.equations @?= Just result
        , testCase "Pure entries learned during predicate simplification are kept" $ do
            ns <- noSolver
            let predicate =
                    Predicate $
                        EqualsK
                            (KSeq someSort [trm| f1{}(con2{}(B:SomeSort{})) |])
                            (KSeq someSort [trm| B:SomeSort{} |])
                pat = (Pattern_ [trm| con1{}(A:SomeSort{}) |]){constraints = Set.singleton predicate}
            (_, cache) <- runNoLoggingT $ evaluatePattern funDef Nothing ns mempty pat
            Map.lookup [trm| f1{}(con2{}(B:SomeSort{})) |] cache.pureEquations
                @?= Just [trm| con2{}(B:SomeSort{}) |]
        ]
  where
    subj = [trm| f1{}(con2{}(A:SomeSort{})) |]
    result = [trm| con2{}(A:SomeSort{}) |]
    marker = [trm| con1{}(\dv{SomeSort{}}("marker")) |]

    evalWithCache def cache t = do
        ns <- noSolver
        runNoLoggingT $ evaluateTerm BottomUp def Nothing ns cache mempty t

test_errors :: TestTree
test_errors =
    testGroup
        "Error cases"
        [ testCase "Simplification enters a loop" $ do
            let a = var "A" someSort
                f = app f1 . (: [])
                subj = f $ app con1 [a]
                loopTerms =
                    [f $ app con1 [a], f $ app con2 [a], f $ app con3 [a, a], f $ app con1 [a]]
            ns <- noSolver
            isLoop loopTerms
                =<< ( runNoLoggingT $
                        fst
                            <$> evaluateTerm TopDown loopDef Nothing ns mempty mempty subj
                    )
        ]
  where
    isLoop ts (Left (EquationLoop ts')) = ts @?= ts'
    isLoop _ (Left err) = assertFailure $ "Unexpected error " <> show err
    isLoop _ (Right r) = assertFailure $ "Unexpected result " <> show r

----------------------------------------

index :: (ByteString -> CellIndex) -> SymbolName -> TermIndex
index constr = TermIndex . (: []) . constr

funDef, simplDef, loopDef :: KoreDefinition
funDef =
    testDefinition
        { functionEquations =
            mkTheory
                [ (index IdxFun "f1", f1Equations)
                , (index IdxFun "f2", f2Equations) -- should not be applied (f2 partial)
                ]
        }
simplDef =
    testDefinition
        { simplifications =
            mkTheory
                [
                    ( index IdxCons "con1"
                    ,
                        [ equation -- con1(con2(f2(X))) => con1(X) , but f2 partial => not applied
                            Nothing
                            [trm| con1{}(con2{}(f2{}(X:SomeSort{}))) |]
                            [trm| con1{}(X:SomeSort{}) |]
                            40
                            `withComputedAttributes` ComputedAxiomAttributes False [UndefinedSymbol "f2"]
                        , equation -- con1(con2(f1(X))) => con1(X)
                            Nothing
                            [trm| con1{}(con2{}(f1{}(X:SomeSort{}))) |]
                            [trm| con1{}(con2{}(X:SomeSort{})) |]
                            40
                        , equation -- con1(con2(X)) => con2(X)
                            Nothing
                            [trm| con1{}(con2{}(X:SomeSort{})) |]
                            [trm| con2{}(X:SomeSort{}) |]
                            50
                        ]
                    )
                ,
                    ( index IdxCons "con3"
                    ,
                        [ equation -- con3(X, X) => inj{sub,some}(con4(X, X))
                            Nothing
                            [trm| con3{}(X:SomeSort{}, X:SomeSort{}) |]
                            [trm| inj{AnotherSort{}, SomeSort{}}(con4{}(X:SomeSort{}, X:SomeSort{})) |]
                            50
                        ]
                    )
                ]
        }
loopDef =
    -- f1(con1(X)) => f1(con2(X)) => f1(con3(X, X)) => f1(con1(X))
    testDefinition
        { simplifications =
            mkTheory
                [
                    ( index IdxFun "f1"
                    ,
                        [ equation
                            Nothing
                            [trm| f1{}(con1{}(X:SomeSort{})) |]
                            [trm| f1{}(con2{}(X:SomeSort{})) |]
                            50
                        , equation
                            Nothing
                            [trm| f1{}(con2{}(X:SomeSort{})) |]
                            [trm| f1{}(con3{}(X:SomeSort{}, X:SomeSort{})) |]
                            50
                        , equation
                            Nothing
                            [trm| f1{}(con3{}(X:SomeSort{}, Y:SomeSort{})) |]
                            [trm| f1{}(con1{}(X:SomeSort{})) |]
                            50
                        ]
                    )
                ]
        }

-- f1(X) => X, but guarded by a (trivially true) requires clause,
-- resp. an (unclear, hence retained) ensures clause
requiresDef, ensuresDef :: KoreDefinition
requiresDef =
    testDefinition
        { functionEquations =
            mkTheory
                [
                    ( index IdxFun "f1"
                    ,
                        [ equation
                            (Just "f1-is-identity-with-requires")
                            [trm| f1{}(X:SomeSort{}) |]
                            [trm| X:SomeSort{} |]
                            50
                            `withRequires` [trivialTruth]
                        ]
                    )
                ]
        }
ensuresDef =
    testDefinition
        { functionEquations =
            mkTheory
                [
                    ( index IdxFun "f1"
                    ,
                        [ equation
                            (Just "f1-is-identity-with-ensures")
                            [trm| f1{}(X:SomeSort{}) |]
                            [trm| X:SomeSort{} |]
                            50
                            `withEnsures` [unclearCondition]
                        ]
                    )
                ]
        }

-- X ==K X: simplifies to true via the ==K hook once instantiated
trivialTruth :: Predicate
trivialTruth =
    Predicate $
        EqualsK
            (KSeq someSort [trm| X:SomeSort{} |])
            (KSeq someSort [trm| X:SomeSort{} |])

-- f2(X) ==K X: cannot be decided (f2 is partial and stays
-- unevaluated), so it is retained as a new path condition
unclearCondition :: Predicate
unclearCondition =
    Predicate $
        EqualsK
            (KSeq someSort [trm| f2{}(X:SomeSort{}) |])
            (KSeq someSort [trm| X:SomeSort{} |])

f1Equations, f2Equations :: [RewriteRule t]
f1Equations =
    [ equation -- f1(con1(X)) == con2(f1(X))
        (Just "f1-con1-is-con2")
        [trm| f1{}(con1{}(X:SomeSort{})) |]
        [trm| con2{}(f1{}(X:SomeSort{})) |]
        42
        `withAttributes` (\as -> as{concreteness = AllConstrained Symbolic})
    , equation -- f1(inj{aSubsort,someSort}(con4(X, _Y))) == X
        (Just "f1-con4-projects-arg1")
        [trm| f1{}(inj{AnotherSort{},SomeSort{}}(con4{}(X:SomeSort{}, Y:SomeSort{}))) |]
        [trm| X:SomeSort{} |]
        42
    , equation -- f1(X) == X
        (Just "f1-is-identity")
        [trm| f1{}(X:SomeSort{}) |]
        [trm| X:SomeSort{} |]
        50
        `withAttributes` (\as -> as{concreteness = SomeConstrained (Map.singleton ("X", "SomeSort") Symbolic)})
    ]
f2Equations =
    [ equation
        Nothing
        [trm| f2{}(con1{}(X:SomeSort{})) |]
        [trm| f2{}(X:SomeSort{}) |]
        42
        `withAttributes` (\as -> as{concreteness = SomeConstrained (Map.singleton ("X", "SomeSort") Concrete)})
    , equation
        Nothing
        [trm| f2{}(X:SomeSort{}) |]
        [trm| con4{}(X:SomeSort{}, X:SomeSort{}) |]
        50
        `withComputedAttributes` ComputedAxiomAttributes False [UndefinedSymbol "f2"]
    ]

equation :: Maybe Text -> Term -> Term -> Priority -> RewriteRule t
equation ruleLabel lhs rhs priority =
    RewriteRule
        { lhs = lhs
        , rhs = rhs
        , requires = mempty
        , ensures = mempty
        , attributes =
            AxiomAttributes
                { location = Nothing
                , priority
                , ruleLabel
                , simplification = Flag False
                , preserving = Flag False
                , concreteness = Unconstrained
                , uniqueId = mockUniqueId
                , smtLemma = Flag False
                }
        , computedAttributes = ComputedAxiomAttributes False []
        , existentials = mempty
        }

withAttributes :: RewriteRule t -> (AxiomAttributes -> AxiomAttributes) -> RewriteRule t
r@RewriteRule{lhs, attributes, computedAttributes} `withAttributes` f =
    r{lhs, computedAttributes, attributes = f attributes}

withComputedAttributes :: RewriteRule t -> ComputedAxiomAttributes -> RewriteRule t
r@RewriteRule{lhs} `withComputedAttributes` computedAttributes =
    r{lhs, computedAttributes}

withRequires, withEnsures :: RewriteRule t -> [Predicate] -> RewriteRule t
r@RewriteRule{lhs} `withRequires` requires = r{lhs, requires}
r@RewriteRule{lhs} `withEnsures` ensures = r{lhs, ensures}

mkTheory :: [(TermIndex, [RewriteRule t])] -> Theory (RewriteRule t)
mkTheory = Map.map mkPriorityGroups . Map.fromList
  where
    mkPriorityGroups :: [RewriteRule t] -> Map Priority [RewriteRule t]
    mkPriorityGroups rules =
        Map.unionsWith
            (<>)
            [Map.fromList [(r.attributes.priority, [r])] | r <- rules]
