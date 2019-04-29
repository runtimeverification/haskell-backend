module Test.Kore.Step.Simplification.Floor
    ( test_floorSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Kore.AST.Common
                 ( Floor (..) )
import           Kore.AST.Valid
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeEqualsPredicate, makeFloorPredicate,
                 makeTruePredicate )
import           Kore.Step.OrPattern
                 ( OrPattern )
import qualified Kore.Step.OrPattern as OrPattern
import           Kore.Step.Pattern
                 ( Conditional (..), Pattern )
import qualified Kore.Step.Pattern as Pattern
                 ( bottom, top )
import           Kore.Step.Simplification.Floor
                 ( makeEvaluateFloor, simplify )
import           Kore.Step.TermLike
import qualified Kore.Unification.Substitution as Substitution

import Test.Kore
       ( testId )
import Test.Kore.Comparators ()
import Test.Kore.Step.MockSymbols
       ( testSort )
import Test.Tasty.HUnit.Extensions

test_floorSimplification :: [TestTree]
test_floorSimplification =
    [ testCase "Floor - or distribution"
        -- floor(a or b) = (top and floor(a)) or (top and floor(b))
        (assertEqualWithExplanation ""
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
            assertEqualWithExplanation "floor(top)"
                (OrPattern.fromPatterns
                    [ Pattern.top ]
                )
                (evaluate
                    (makeFloor
                        [Pattern.top]
                    )
                )
            -- floor(bottom) = bottom
            assertEqualWithExplanation "floor(bottom)"
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
            assertEqualWithExplanation "floor(top)"
                (OrPattern.fromPatterns
                    [ Pattern.top ]
                )
                (makeEvaluate
                    (Pattern.top :: Pattern Object Variable)
                )
            -- floor(bottom) = bottom
            assertEqualWithExplanation "floor(bottom)"
                (OrPattern.fromPatterns
                    []
                )
                (makeEvaluate
                    (Pattern.bottom :: Pattern Object Variable)
                )
        )
    , testCase "floor with predicates and substitutions"
        -- floor(term and predicate and subst)
        --     = top and (floor(term) and predicate) and subst
        (assertEqualWithExplanation "floor(top)"
            (OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate =
                        makeAndPredicate
                            (makeFloorPredicate a)
                            (makeEqualsPredicate fOfA gOfA)
                    , substitution = Substitution.wrap [(x, fOfB)]
                    }
                ]
            )
            (makeEvaluate
                Conditional
                    { term = a
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution = Substitution.wrap [(x, fOfB)]
                    }
            )
        )
    -- floor moves predicates and substitutions up
    ]
  where
    fId = testId "f"
    gId = testId "g"
    aSymbol = SymbolOrAlias
        { symbolOrAliasConstructor = testId "a"
        , symbolOrAliasParams      = []
        }
    bSymbol = SymbolOrAlias
        { symbolOrAliasConstructor = testId "b"
        , symbolOrAliasParams      = []
        }
    fSymbol = SymbolOrAlias
        { symbolOrAliasConstructor = fId
        , symbolOrAliasParams      = []
        }
    gSymbol = SymbolOrAlias
        { symbolOrAliasConstructor = gId
        , symbolOrAliasParams      = []
        }
    x = Variable (testId "x") mempty testSort
    a :: TermLike Variable
    a = mkApp testSort aSymbol []
    b :: TermLike Variable
    b = mkApp testSort bSymbol []
    fOfA = mkApp testSort fSymbol [a]
    fOfB = mkApp testSort fSymbol [b]
    gOfA = mkApp testSort gSymbol [a]
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
    => [Pattern Object variable]
    -> Floor Object (OrPattern Object variable)
makeFloor patterns =
    Floor
        { floorOperandSort = testSort
        , floorResultSort  = testSort
        , floorChild       = OrPattern.fromPatterns patterns
        }

evaluate
    :: Floor Object (OrPattern Object Variable)
    -> OrPattern Object Variable
evaluate floor' =
    case simplify floor' of
        (result, _proof) -> result


makeEvaluate :: Pattern Object Variable -> OrPattern Object Variable
makeEvaluate child =
    case makeEvaluateFloor child of
        (result, _proof) -> result
