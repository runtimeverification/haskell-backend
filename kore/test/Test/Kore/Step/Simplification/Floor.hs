module Test.Kore.Step.Simplification.Floor
    ( test_floorSimplification
    ) where

import Test.Tasty

import qualified Data.Default as Default

import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Conditional (..)
    , Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
    ( bottom
    , top
    )
import Kore.Internal.Symbol
import Kore.Internal.TermLike
import Kore.Predicate.Predicate
    ( makeAndPredicate
    , makeEqualsPredicate
    , makeFloorPredicate
    , makeTruePredicate
    )
import Kore.Step.Simplification.Floor
    ( makeEvaluateFloor
    , simplify
    )
import qualified Kore.Unification.Substitution as Substitution
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import Test.Kore
    ( testId
    )
import Test.Kore.Step.MockSymbols
    ( testSort
    )
import Test.Tasty.HUnit.Ext

test_floorSimplification :: [TestTree]
test_floorSimplification =
    [ testCase "Floor - or distribution"
        -- floor(a or b) = (top and floor(a)) or (top and floor(b))
        (assertEqual ""
            (OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate = makeFloorPredicate (mkOr a b)
                    , substitution = mempty
                    }
                ]
            )
            (evaluate
                (makeFloor
                    [aExpanded, bExpanded]
                )
            )
        )
    , testCase "Floor - bool operations"
        (do
            -- floor(top) = top
            assertEqual "floor(top)"
                (OrPattern.fromPatterns
                    [ Pattern.top ]
                )
                (evaluate
                    (makeFloor
                        [Pattern.top]
                    )
                )
            -- floor(bottom) = bottom
            assertEqual "floor(bottom)"
                (OrPattern.fromPatterns
                    []
                )
                (evaluate
                    (makeFloor
                        []
                    )
                )
        )
    , testCase "expanded Floor - bool operations"
        (do
            -- floor(top) = top
            assertEqual "floor(top)"
                (OrPattern.fromPatterns
                    [ Pattern.top ]
                )
                (makeEvaluate
                    (Pattern.top :: Pattern Variable)
                )
            -- floor(bottom) = bottom
            assertEqual "floor(bottom)"
                (OrPattern.fromPatterns
                    []
                )
                (makeEvaluate
                    (Pattern.bottom :: Pattern Variable)
                )
        )
    , testCase "floor with predicates and substitutions"
        -- floor(term and predicate and subst)
        --     = top and (floor(term) and predicate) and subst
        (assertEqual "floor(top)"
            (OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate =
                        makeAndPredicate
                            (makeFloorPredicate a)
                            (makeEqualsPredicate fOfA gOfA)
                    , substitution = Substitution.wrap [(ElemVar x, fOfB)]
                    }
                ]
            )
            (makeEvaluate
                Conditional
                    { term = a
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution = Substitution.wrap [(ElemVar x, fOfB)]
                    }
            )
        )
    -- floor moves predicates and substitutions up
    ]
  where
    symbol name operands result =
        Symbol
            { symbolConstructor = testId name
            , symbolParams = []
            , symbolAttributes = Default.def
            , symbolSorts = applicationSorts operands result
            }
    aSymbol = symbol "a" [] testSort
    bSymbol = symbol "b" [] testSort
    fSymbol = symbol "f" [testSort] testSort
    gSymbol = symbol "g" [testSort] testSort
    x = ElementVariable $ Variable (testId "x") mempty testSort
    a :: TermLike Variable
    a = mkApplySymbol aSymbol []
    b :: TermLike Variable
    b = mkApplySymbol bSymbol []
    fOfA = mkApplySymbol fSymbol [a]
    fOfB = mkApplySymbol fSymbol [b]
    gOfA = mkApplySymbol gSymbol [a]
    aExpanded = Conditional
        { term = a
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    bExpanded = Conditional
        { term = b
        , predicate = makeTruePredicate
        , substitution = mempty
        }

makeFloor
    :: Ord variable
    => [Pattern variable]
    -> Floor Sort (OrPattern variable)
makeFloor patterns =
    Floor
        { floorOperandSort = testSort
        , floorResultSort  = testSort
        , floorChild       = OrPattern.fromPatterns patterns
        }

evaluate :: Floor Sort (OrPattern Variable) -> OrPattern Variable
evaluate = simplify

makeEvaluate :: Pattern Variable -> OrPattern Variable
makeEvaluate = makeEvaluateFloor
