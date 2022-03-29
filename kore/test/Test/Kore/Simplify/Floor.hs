module Test.Kore.Simplify.Floor (
    test_floorSimplification,
) where

import Data.Default qualified as Default
import Kore.Internal.Condition qualified as Condition (
    top,
 )
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Pattern (
    Conditional (..),
    Pattern,
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.Predicate (
    makeAndPredicate,
    makeEqualsPredicate,
    makeFloorPredicate,
    makeTruePredicate,
 )
import Kore.Internal.Substitution qualified as Substitution
import Kore.Internal.Symbol
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    mkConfigVariable,
 )
import Kore.Simplify.Floor (
    makeEvaluateFloor,
    simplify,
 )
import Prelude.Kore
import Test.Kore (
    testId,
 )
import Test.Kore.Rewrite.MockSymbols (
    subSort,
    testSort,
 )
import Test.Kore.Simplify
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_floorSimplification :: [TestTree]
test_floorSimplification =
    [ testCase
        "Floor - or distribution"
        -- floor(a or b) = (top and floor(a)) or (top and floor(b))
        ( assertEqual
            ""
            ( OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop testSort
                    , predicate = makeFloorPredicate (mkOr a b)
                    , substitution = mempty
                    }
                ]
            )
            ( evaluate
                ( makeFloor
                    [aExpanded, bExpanded]
                )
            )
        )
    , testCase
        "Floor - bool operations"
        ( do
            -- floor(top) = top
            assertEqual
                "floor(top)"
                ( OrPattern.fromPatterns
                    [Pattern.topOf testSort]
                )
                ( evaluate
                    ( makeFloor
                        [Pattern.topOf subSort]
                    )
                )
            -- floor(bottom) = bottom
            assertEqual
                "floor(bottom)"
                ( OrPattern.fromPatterns
                    []
                )
                ( evaluate
                    ( makeFloor
                        []
                    )
                )
        )
    , testCase "Floor - bool operations" $
        -- floor(top{testSort}) = top
        assertEqual
            "floor(top)"
            ( OrPattern.fromPatterns
                [Pattern.topOf testSort]
            )
            ( evaluate
                ( makeFloor
                    [Pattern.fromCondition testSort Condition.top]
                )
            )
    , testCase
        "expanded Floor - bool operations"
        ( do
            -- floor(top) = top
            assertEqual
                "floor(top)"
                ( OrPattern.fromPatterns
                    [Pattern.topOf testSort]
                )
                ( makeEvaluate
                    testSort
                    (Pattern.topOf subSort :: Pattern RewritingVariableName)
                )
            -- floor(bottom) = bottom
            assertEqual
                "floor(bottom)"
                OrPattern.bottom
                ( makeEvaluate
                    testSort
                    (Pattern.bottomOf subSort :: Pattern RewritingVariableName)
                )
        )
    , testCase
        "floor with predicates and substitutions"
        -- floor(term and predicate and subst)
        --     = top and (floor(term) and predicate) and subst
        ( assertEqual
            "floor(top)"
            ( OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop testSort
                    , predicate =
                        makeAndPredicate
                            (makeFloorPredicate a)
                            (makeEqualsPredicate fOfA gOfA)
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [(inject x, fOfB)]
                    }
                ]
            )
            ( makeEvaluate
                testSort
                Conditional
                    { term = a
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [(inject x, fOfB)]
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
    x =
        mkElementVariable (testId "x") testSort
            & mapElementVariable (pure mkConfigVariable)
    a :: TermLike RewritingVariableName
    a = mkApplySymbol aSymbol []
    b :: TermLike RewritingVariableName
    b = mkApplySymbol bSymbol []
    fOfA = mkApplySymbol fSymbol [a]
    fOfB = mkApplySymbol fSymbol [b]
    gOfA = mkApplySymbol gSymbol [a]
    aExpanded =
        Conditional
            { term = a
            , predicate = makeTruePredicate
            , substitution = mempty
            }
    bExpanded =
        Conditional
            { term = b
            , predicate = makeTruePredicate
            , substitution = mempty
            }

makeFloor ::
    [Pattern RewritingVariableName] ->
    Floor Sort (OrPattern RewritingVariableName)
makeFloor patterns =
    Floor
        { floorOperandSort = testSort
        , floorResultSort = testSort
        , floorChild = OrPattern.fromPatterns patterns
        }

evaluate ::
    Floor Sort (OrPattern RewritingVariableName) ->
    OrPattern RewritingVariableName
evaluate = simplify . fmap simplifiedOrPattern

makeEvaluate ::
    Sort ->
    Pattern RewritingVariableName ->
    OrPattern RewritingVariableName
makeEvaluate sort = makeEvaluateFloor sort . simplifiedPattern
