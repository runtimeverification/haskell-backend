module Test.Kore.Step.Simplification.Forall
    ( test_forallSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import Data.Reflection
       ( Given, give )

import           Kore.AST.Common
                 ( AstLocation (..), Forall (..), Id (..), Sort (..),
                 SortActual (..), Variable )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkAnd, mkApp, mkCeil, mkEquals, mkForall, mkVar )
import           Kore.IndexedModule.MetadataTools
                 ( SortTools )
import           Kore.Predicate.Predicate
                 ( makeCeilPredicate, makeEqualsPredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), bottom, top )
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern, OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import qualified Kore.Step.Simplification.Forall as Forall
                 ( makeEvaluate, simplify )

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeSortTools )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_forallSimplification :: [TestTree]
test_forallSimplification = give mockSortTools
    [ testCase "Forall - or distribution"
        -- forall(a or b) = forall(a) or forall(b)
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkForall Mock.x something1OfX
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                , ExpandedPattern
                    { term = mkForall Mock.x something2OfX
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ]
            )
            (evaluate
                (makeForall
                    Mock.x
                    [something1OfXExpanded, something2OfXExpanded]
                )
            )
        )
    , testCase "Forall - bool operations"
        (do
            -- forall(top) = top
            assertEqualWithExplanation "forall(top)"
                (OrOfExpandedPattern.make
                    [ ExpandedPattern.top ]
                )
                (evaluate
                    (makeForall
                        Mock.x
                        [ExpandedPattern.top]
                    )
                )
            -- forall(bottom) = bottom
            assertEqualWithExplanation "forall(bottom)"
                (OrOfExpandedPattern.make
                    []
                )
                (evaluate
                    (makeForall
                        Mock.x
                        []
                    )
                )
        )
    , testCase "expanded Forall - bool operations"
        (do
            -- forall(top) = top
            assertEqualWithExplanation "forall(top)"
                ExpandedPattern.top
                (makeEvaluate
                    Mock.x
                    (ExpandedPattern.top :: CommonExpandedPattern Object)
                )
            -- forall(bottom) = bottom
            assertEqualWithExplanation "forall(bottom)"
                ExpandedPattern.bottom
                (makeEvaluate
                    Mock.x
                    (ExpandedPattern.bottom :: CommonExpandedPattern Object)
                )
        )
    , testCase "forall applies substitution if possible"
        -- forall x . (t(x) and p(x) and [x = alpha, others])
        (assertEqualWithExplanation "forall with substitution"
            ExpandedPattern
                { term =
                    mkForall Mock.x
                        (mkAnd
                            (mkAnd
                                (mkApp Mock.fSymbol [mkVar Mock.x])
                                (mkCeil (Mock.h (mkVar Mock.x)))
                            )
                            (mkAnd
                                (mkEquals (mkVar Mock.x) gOfA)
                                (mkEquals (mkVar Mock.y) fOfA)
                            )
                        )
                , predicate = makeTruePredicate
                , substitution = []
                }
            (makeEvaluate
                Mock.x
                ExpandedPattern
                    { term = mkApp Mock.fSymbol [mkVar Mock.x]
                    , predicate = makeCeilPredicate (Mock.h (mkVar Mock.x))
                    , substitution = [(Mock.x, gOfA), (Mock.y, fOfA)]
                    }
            )
        )
    , testCase "forall disappears if variable not used"
        -- forall x . (t and p and s)
        (assertEqualWithExplanation "forall with substitution"
            ExpandedPattern
                { term =
                    mkForall Mock.x (mkAnd fOfA (mkCeil gOfA))
                , predicate = makeTruePredicate
                , substitution = []
                }
            (makeEvaluate
                Mock.x
                ExpandedPattern
                    { term = fOfA
                    , predicate = makeCeilPredicate gOfA
                    , substitution = []
                    }
            )
        )
    , testCase "forall applied on term if not used elsewhere"
        -- forall x . (t(x) and p and s)
        (assertEqualWithExplanation "forall on term"
            ExpandedPattern
                { term = mkForall Mock.x (mkAnd fOfX (mkCeil gOfA))
                , predicate = makeTruePredicate
                , substitution = []
                }
            (makeEvaluate
                Mock.x
                ExpandedPattern
                    { term = fOfX
                    , predicate = makeCeilPredicate gOfA
                    , substitution = []
                    }
            )
        )
    , testCase "forall applied on predicate if not used elsewhere"
        -- forall x . (t and p(x) and s)
        --    = t and (forall x . p(x)) and s
        --    if t, s do not depend on x.
        (assertEqualWithExplanation "forall on predicate"
            ExpandedPattern
                { term = mkForall Mock.x (mkAnd fOfA (mkCeil fOfX))
                , predicate = makeTruePredicate
                , substitution = []
                }
            (makeEvaluate
                Mock.x
                ExpandedPattern
                    { term = fOfA
                    , predicate = makeCeilPredicate fOfX
                    , substitution = []
                    }
            )
        )
    , testCase "forall moves substitution above"
        -- forall x . (t(x) and p(x) and s)
        (assertEqualWithExplanation "forall moves substitution"
            ExpandedPattern
                { term =
                    mkForall Mock.x
                        (mkAnd
                            (mkAnd fOfX (mkEquals fOfX gOfA))
                            (mkEquals (mkVar Mock.y) hOfA)
                        )
                , predicate = makeTruePredicate
                , substitution = []
                }
            (makeEvaluate
                Mock.x
                ExpandedPattern
                    { term = fOfX
                    , predicate = makeEqualsPredicate fOfX gOfA
                    , substitution = [(Mock.y, hOfA)]
                    }
            )
        )
    {-
    Uncomment this if we ever decide to substitute + reevaluate in foralls
    , testCase "forall reevaluates"
        -- forall x . (top and (f(x) = f(g(a)) and [x=g(a)])
        --    = top.s
        (assertEqualWithExplanation "forall reevaluates"
            ExpandedPattern.top
            (makeEvaluate
                Mock.x
                ExpandedPattern
                    { term = mkTop
                    , predicate = makeEqualsPredicate fOfX (Mock.f gOfA)
                    , substitution = [(Mock.x, gOfA)]
                    }
            )
        )
        -}
    ]
  where
    fOfA = give mockSortTools $ Mock.f Mock.a
    fOfX = give mockSortTools $ Mock.f (mkVar Mock.x)
    gOfA = give mockSortTools $ Mock.g Mock.a
    hOfA = give mockSortTools $ Mock.h Mock.a
    something1OfX = give mockSortTools $ Mock.plain10 (mkVar Mock.x)
    something2OfX = give mockSortTools $ Mock.plain11 (mkVar Mock.x)
    something1OfXExpanded = ExpandedPattern
        { term = something1OfX
        , predicate = makeTruePredicate
        , substitution = []
        }
    something2OfXExpanded = ExpandedPattern
        { term = something2OfX
        , predicate = makeTruePredicate
        , substitution = []
        }
    mockSortTools = Mock.makeSortTools Mock.sortToolsMapping

makeForall
    :: variable Object
    -> [ExpandedPattern Object variable]
    -> Forall Object variable (OrOfExpandedPattern Object variable)
makeForall variable patterns =
    Forall
        { forallSort = testSort
        , forallVariable  = variable
        , forallChild       = OrOfExpandedPattern.make patterns
        }

testSort :: Sort Object
testSort =
    SortActualSort SortActual
        { sortActualName  = Id "testSort" AstLocationTest
        , sortActualSorts = []
        }

evaluate
    ::  ( MetaOrObject level
        , Given (SortTools level)
        )
    => Forall level Variable (CommonOrOfExpandedPattern level)
    -> CommonOrOfExpandedPattern level
evaluate forall =
    fst $ Forall.simplify forall

makeEvaluate
    ::  ( MetaOrObject level
        , Given (SortTools level)
        )
    => Variable level
    -> CommonExpandedPattern level
    -> CommonExpandedPattern level
makeEvaluate variable child =
    fst $ Forall.makeEvaluate variable child

