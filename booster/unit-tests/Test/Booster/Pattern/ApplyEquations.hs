{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Test.Booster.Pattern.ApplyEquations (
    test_evaluateFunction,
    test_simplify,
    test_errors,
) where

import Data.Map (Map)
import Data.Map qualified as Map
import Data.Text (Text)
import Test.Tasty
import Test.Tasty.HUnit

import Booster.Definition.Attributes.Base
import Booster.Definition.Base
import Booster.Pattern.ApplyEquations
import Booster.Pattern.Base
import Booster.Pattern.Index (TermIndex (..))
import Test.Booster.Fixture

test_evaluateFunction :: TestTree
test_evaluateFunction =
    testGroup
        "Evaluating functions using rules without side conditions"
        [ -- f1(a) => a
          testCase "Simple function evaluation" $ do
            let subj = app f1 [a]
            eval TopDown subj @?= Right a
            eval BottomUp subj @?= Right a
        , -- f2(f1(f1(a))) => f2(a). f2 is marked as partial, so not evaluating
          testCase "Nested function applications, one not to be evaluated" $ do
            let subj = app f2 [2 `times` f1 $ a]
            eval TopDown subj @?= Right (app f2 [a])
            eval BottomUp subj @?= Right (app f2 [a])
        , -- f1(f2(f1(a))) => f2(a). Again f2 partial, so not evaluating
          testCase "Nested function applications with partial function inside" $ do
            let subj = app f1 [app f2 [app f1 [a]]]
            eval TopDown subj @?= Right (app f2 [a])
            eval BottomUp subj @?= Right (app f2 [a])
        , -- f1(con1(con1(..con1(a)..))) => con2(con2(..con2(a)..))
          testCase "Recursive evaluation" $ do
            let subj depth = app f1 [iterate (apply con1) a !! depth]
            -- top-down evaluation: a single iteration is enough
            eval TopDown (subj 101) @?= Right (101 `times` con2 $ a)
            -- bottom-up evaluation: `depth` many iterations
            eval BottomUp (subj 100) @?= Right (100 `times` con2 $ a)
            isTooManyIterations $ eval BottomUp (subj 101)
        , -- con3(f1(a), f1(con1(b))) => con3(a, con2(b))
          testCase "Several function calls inside a constructor" $ do
            let subj = app con3 [app f1 [a], app f1 [app con1 [b]]]
                result = app con3 [a, app con2 [b]]
            eval TopDown subj @?= Right result
        , -- f1(inj{sub,some}(con4(a, b))) => f1(a) => a (not using f1-is-identity)
          testCase "Matching uses priorities" $ do
            let subj = app f1 [inj aSubsort someSort (app con4 [a, b])]
            eval TopDown subj @?= Right a
        ]
  where
    eval direction = fmap fst . evaluateTerm direction funDef Nothing
    a = var "A" someSort
    b = var "B" someSort
    apply f = app f . (: [])
    n `times` f = foldr (.) id (replicate n $ apply f)

    isTooManyIterations (Left (TooManyIterations _n _ _)) = pure ()
    isTooManyIterations (Left err) = assertFailure $ "Unexpected error " <> show err
    isTooManyIterations (Right r) = assertFailure $ "Unexpected result" <> show r

test_simplify :: TestTree
test_simplify =
    testGroup
        "Performing simplifications"
        [ testCase "No simplification applies" $ do
            let subj = app f1 [app f2 [a]]
            simpl TopDown subj @?= Right subj
            simpl BottomUp subj @?= Right subj
        , -- con1(con2(f2(a))) => con2(f2(a))
          testCase "Simplification of constructors" $ do
            let subj = app con1 [app con2 [app f2 [a]]]
            simpl TopDown subj @?= Right (app con2 [app f2 [a]])
            simpl BottomUp subj @?= Right (app con2 [app f2 [a]])
        , -- con3(f2(a), f2(a)) => inj{sub,some}(con4(f2(a), f2(a)))
          testCase "Simplification with argument match" $ do
            let f2a = app f2 [a]
                subj = app con3 [f2a, f2a]
                result = inj aSubsort someSort $ app con4 [f2a, f2a]
            simpl TopDown subj @?= Right result
            simpl BottomUp subj @?= Right result
        ]
  where
    simpl direction = fmap fst . evaluateTerm direction simplDef Nothing
    a = var "A" someSort

test_errors :: TestTree
test_errors =
    testGroup
        "Error cases"
        [ testCase "Simplification enters a loop" $ do
            let a = var "A" someSort
                f = app f1 . (: [])
                subj = f $ app con1 [a]
                result =
                    EquationLoop
                        [f $ app con1 [a], f $ app con2 [a], f $ app con3 [a, a], f $ app con1 [a]]
            evaluateTerm TopDown loopDef Nothing subj @?= Left result
        ]

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
                            (Pattern (app con1 [app con2 [app f2 [varX]]]) [])
                            (Pattern (app con1 [varX]) [])
                            40
                            `withComputedAttributes` ComputedAxiomAttributes False [UndefinedSymbol "f2"]
                        , equation -- con1(con2(f1(X))) => con3(X, X)
                            Nothing
                            (Pattern (app con1 [app con2 [app f1 [varX]]]) [])
                            (Pattern (app con1 [varX]) [])
                            40
                        , equation -- con1(con2(X)) => con2(X)
                            Nothing
                            (Pattern (app con1 [app con2 [varX]]) [])
                            (Pattern (app con2 [varX]) [])
                            50
                        ]
                    )
                ,
                    ( TopSymbol "con3"
                    ,
                        [ equation -- con3(X, X) => inj{sub,some}(con4(X, X))
                            Nothing
                            (Pattern (app con3 [varX, varX]) [])
                            (Pattern (inj aSubsort someSort $ app con4 [varX, varX]) [])
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
                            (Pattern (app f1 [app con1 [varX]]) [])
                            (Pattern (app f1 [app con2 [varX]]) [])
                            50
                        , equation
                            Nothing
                            (Pattern (app f1 [app con2 [varX]]) [])
                            (Pattern (app f1 [app con3 [varX, varX]]) [])
                            50
                        , equation
                            Nothing
                            (Pattern (app f1 [app con3 [varX, varY]]) [])
                            (Pattern (app f1 [app con1 [varX]]) [])
                            50
                        ]
                    )
                ]
        }

varX, varY :: Term
varX = var "X" someSort
varY = var "Y" someSort

f1Equations, f2Equations :: [RewriteRule t]
f1Equations =
    [ equation -- f1(con1(X)) == con2(f1(X))
        (Just "f1-con1-is-con2")
        (Pattern (app f1 [app con1 [varX]]) [])
        (Pattern (app con2 [app f1 [varX]]) [])
        42
    , equation -- f1(inj{aSubsort,someSort}(con4(X, _Y))) == X
        (Just "f1-con4-projects-arg1")
        (Pattern (app f1 [inj aSubsort someSort (app con4 [varX, varY])]) [])
        (Pattern varX [])
        42
    , equation -- f1(X) == X
        (Just "f1-is-identity")
        (Pattern (app f1 [varX]) [])
        (Pattern varX [])
        50
    ]
f2Equations =
    [ equation
        Nothing
        (Pattern (app f2 [varX]) [])
        (Pattern (app con4 [varX, varX]) [])
        50
        `withComputedAttributes` ComputedAxiomAttributes False [UndefinedSymbol "f2"]
    ]

equation :: Maybe Text -> Pattern -> Pattern -> Priority -> RewriteRule t
equation ruleLabel lhs rhs priority =
    RewriteRule
        { lhs = lhs.term
        , rhs = rhs.term
        , requires = lhs.constraints
        , ensures = rhs.constraints
        , attributes =
            AxiomAttributes
                { location = Nothing
                , priority
                , ruleLabel
                , simplification = Flag False
                , preserving = Flag False
                , concreteness = Unconstrained
                }
        , computedAttributes = ComputedAxiomAttributes False []
        , existentials = mempty
        }

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
