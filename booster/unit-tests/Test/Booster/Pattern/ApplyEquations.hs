{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Test.Booster.Pattern.ApplyEquations (
    test_evaluateFunction,
    test_simplify,
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
            eval TopDown (subj 100) @?= Right (100 `times` con2 $ a)
            -- bottom-up evaluation: `depth` many iterations
            eval BottomUp (subj 99) @?= Right (99 `times` con2 $ a)
            isTooManyIterations $ eval BottomUp (subj 100)
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
    eval direction = evaluateFunctions direction def Nothing
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
        []

----------------------------------------

def :: KoreDefinition
def =
    testDefinition
        { functionEquations =
            mkTheory
                [ (TopSymbol "f1", f1Equations)
                , (TopSymbol "f2", f2Equations)
                ]
        }

varX, varY :: Term
varX = var "X" someSort
varY = var "Y" someSort

f1Equations, f2Equations :: [RewriteRule "Function"]
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
        `withComputedAttributes` ComputedAxiomAttributes False False
    ]

equation :: Maybe Text -> Pattern -> Pattern -> Priority -> RewriteRule t
equation ruleLabel lhs rhs priority =
    RewriteRule
        { lhs
        , rhs
        , attributes =
            AxiomAttributes
                { location = Nothing
                , priority
                , ruleLabel
                , simplification = Nothing
                , preserving = Nothing
                }
        , computedAttributes = ComputedAxiomAttributes False True
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
