{-# LANGUAGE QuasiQuotes #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Test.Booster.Pattern.ApplyEquations (
    test_evaluateFunction,
    test_simplify,
    test_simplifyPattern,
    test_errors,
) where

import Control.Monad.Logger (runNoLoggingT)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Text (Text)
import GHC.IO.Unsafe (unsafePerformIO)
import Test.Tasty
import Test.Tasty.HUnit

import Booster.Definition.Attributes.Base
import Booster.Definition.Base
import Booster.Pattern.ApplyEquations
import Booster.Pattern.Base
import Booster.Pattern.Index (TermIndex (..))
import Booster.Syntax.Json.Internalise (trm)
import Test.Booster.Fixture hiding (inj)

inj :: Symbol
inj = injectionSymbol

test_evaluateFunction :: TestTree
test_evaluateFunction =
    testGroup
        "Evaluating functions using rules without side conditions"
        [ -- f1(a) => a
          testCase "Simple function evaluation" $ do
            eval TopDown [trm| f1{}(con2{}(A:SomeSort{})) |] @?= Right [trm| con2{}(A:SomeSort{}) |]
            eval BottomUp [trm| f1{}(con2{}(A:SomeSort{})) |] @?= Right [trm| con2{}(A:SomeSort{}) |]
        , -- f2(f1(f1(con2(a)))) => f2(con2(a)). f2 is marked as partial, so not evaluating
          testCase "Nested function applications, one not to be evaluated" $ do
            let subj = [trm| f2{}(f1{}(f1{}(con2{}(A:SomeSort{})))) |]
                goal = [trm| f2{}(con2{}(A:SomeSort{})) |]
            eval TopDown subj @?= Right goal
            eval BottomUp subj @?= Right goal
        , -- f1(f2(f1(con2(a)))) => f1(f2(con2(a))). Again f2 partial, so not evaluating,
          -- therefore f1(x) => x not applied to unevaluated value
          testCase "Nested function applications with partial function inside" $ do
            let subj = [trm| f1{}(f2{}(f1{}(con2{}(A:SomeSort{})))) |]
                goal = [trm| f1{}(f2{}(con2{}(A:SomeSort{}))) |]
            eval TopDown subj @?= Right goal
            eval BottomUp subj @?= Right goal
        , -- f1(con1(con1(..con1(con2(a))..))) => con2(con2(..con2(a)..))
          -- using f1(con1(X)) => con2(X) repeatedly
          testCase "Recursive evaluation" $ do
            let subj depth = app f1 [iterate (apply con1) a !! depth]
                a = app con2 [var "A" someSort]
                apply f = app f . (: [])
                n `times` f = foldr (.) id (replicate n $ apply f)
            -- top-down evaluation: a single iteration is enough
            eval TopDown (subj 101) @?= Right (101 `times` con2 $ a)
            -- bottom-up evaluation: `depth` many iterations
            eval BottomUp (subj 100) @?= Right (100 `times` con2 $ a)
            isTooManyIterations $ eval BottomUp (subj 101)
        , -- con3(f1(con2(a)), f1(con1(con2(b)))) => con3(con2(a), con2(con2(b)))
          testCase "Several function calls inside a constructor" $ do
            eval TopDown [trm| con3{}(f1{}(con2{}(A:SomeSort{})), f1{}(con1{}(con2{}(B:SomeSort{})))) |]
                @?= Right [trm| con3{}(con2{}(A:SomeSort{}), con2{}(con2{}(B:SomeSort{}))) |]
        , -- f1(inj{sub,some}(con4(a, b))) => f1(a) => a (not using f1-is-identity)
          testCase "Matching uses priorities" $ do
            eval TopDown [trm| f1{}(inj{AnotherSort{}, SomeSort{}}(con4{}(A:SomeSort{}, B:SomeSort{}))) |]
                @?= Right [trm| A:SomeSort{} |]
        , -- f1(con1("hey")) unmodified, since "hey" is concrete
          testCase "f1 with concrete argument, constraints prevent rule application" $ do
            let subj = [trm| f1{}(con1{}( \dv{SomeSort{}}("hey")) ) |]
            eval TopDown subj @?= Right subj
            eval BottomUp subj @?= Right subj
        , testCase "f2 with symbolic argument, constraint prevents rule application" $ do
            let subj = [trm| f2{}(con1{}(A:SomeSort{})) |]
            eval TopDown subj @?= Right subj
            eval BottomUp subj @?= Right subj
        , testCase "f2 with concrete argument, satisfying constraint" $ do
            let subj = [trm| f2{}(con1{}(\dv{SomeSort{}}("hey"))) |]
                result = [trm| f2{}(\dv{SomeSort{}}("hey")) |]
            eval TopDown subj @?= Right result
            eval BottomUp subj @?= Right result
        ]
  where
    eval direction = unsafePerformIO . runNoLoggingT . (fst <$>) . evaluateTerm False direction funDef Nothing

    isTooManyIterations (Left (TooManyIterations _n _ _)) = pure ()
    isTooManyIterations (Left err) = assertFailure $ "Unexpected error " <> show err
    isTooManyIterations (Right r) = assertFailure $ "Unexpected result" <> show r

test_simplify :: TestTree
test_simplify =
    testGroup
        "Performing simplifications"
        [ testCase "No simplification applies" $ do
            let subj = [trm| f1{}(f2{}(A:SomeSort{})) |]
            simpl TopDown subj @?= Right subj
            simpl BottomUp subj @?= Right subj
        , -- con1(con2(f2(a))) => con2(f2(a))
          testCase "Simplification of constructors" $ do
            let subj = app con1 [app con2 [app f2 [a]]]
            simpl TopDown subj @?= Right (app con2 [app f2 [a]])
            simpl BottomUp subj @?= Right (app con2 [app f2 [a]])
        , -- con3(f2(a), f2(a)) => inj{sub,some}(con4(f2(a), f2(a)))
          testCase "Simplification with argument match" $ do
            let subj = [trm| con3{}(f2{}(A:SomeSort{}), f2{}(A:SomeSort{})) |]
                result = [trm| inj{AnotherSort{}, SomeSort{}}(con4{}(f2{}(A:SomeSort{}), f2{}(A:SomeSort{}))) |]
            simpl TopDown subj @?= Right result
            simpl BottomUp subj @?= Right result
        ]
  where
    simpl direction = unsafePerformIO . runNoLoggingT . (fst <$>) . evaluateTerm False direction simplDef Nothing
    a = var "A" someSort

test_simplifyPattern :: TestTree
test_simplifyPattern =
    testGroup
        "Performing simplifications"
        [ testCase "No simplification applies" $ do
            let subj = [trm| f1{}(f2{}(A:SomeSort{})) |]
            simpl Pattern{term = subj, constraints = mempty}
                @?= Right Pattern{term = subj, constraints = mempty}
            simpl Pattern{term = subj, constraints = mempty}
                @?= Right Pattern{term = subj, constraints = mempty}
        , -- con1(con2(f2(a))) => con2(f2(a))
          testCase "Simplification of constructors" $ do
            let subj = app con1 [app con2 [app f2 [a]]]
            simpl Pattern{term = subj, constraints = mempty}
                @?= Right Pattern{term = app con2 [app f2 [a]], constraints = mempty}
            simpl Pattern{term = subj, constraints = mempty}
                @?= Right Pattern{term = app con2 [app f2 [a]], constraints = mempty}
        , -- con3(f2(a), f2(a)) => inj{sub,some}(con4(f2(a), f2(a)))
          testCase "Simplification with argument match" $ do
            let subj = Pattern{term = [trm| con3{}(f2{}(A:SomeSort{}), f2{}(A:SomeSort{})) |], constraints = mempty}
                result =
                    Pattern
                        { term = [trm| inj{AnotherSort{}, SomeSort{}}(con4{}(f2{}(A:SomeSort{}), f2{}(A:SomeSort{}))) |]
                        , constraints = mempty
                        }
            simpl subj @?= Right result
        ]
  where
    simpl = unsafePerformIO . runNoLoggingT . (fst <$>) . evaluatePattern False simplDef Nothing
    a = var "A" someSort

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
            isLoop loopTerms . unsafePerformIO . runNoLoggingT $
                fst <$> evaluateTerm False TopDown loopDef Nothing subj
        ]
  where
    isLoop ts (Left (EquationLoop ts')) = ts @?= ts'
    isLoop _ (Left err) = assertFailure $ "Unexpected error " <> show err
    isLoop _ (Right r) = assertFailure $ "Unexpected result " <> show r

----------------------------------------

funDef, simplDef, loopDef :: KoreDefinition
funDef =
    testDefinition
        { functionEquations =
            mkTheory
                [ (TopSymbol "f1", f1Equations)
                , (TopSymbol "f2", f2Equations) -- should not be applied (f2 partial)
                ]
        }
simplDef =
    testDefinition
        { simplifications =
            mkTheory
                [
                    ( TopSymbol "con1"
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
                    ( TopSymbol "con3"
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
                    ( TopSymbol "f1"
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
                , uniqueId = Nothing
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

mkTheory :: [(TermIndex, [RewriteRule t])] -> Theory (RewriteRule t)
mkTheory = Map.map mkPriorityGroups . Map.fromList
  where
    mkPriorityGroups :: [RewriteRule t] -> Map Priority [RewriteRule t]
    mkPriorityGroups rules =
        Map.unionsWith
            (<>)
            [Map.fromList [(r.attributes.priority, [r])] | r <- rules]
