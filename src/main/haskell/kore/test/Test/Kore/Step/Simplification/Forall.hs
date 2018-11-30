module Test.Kore.Step.Simplification.Forall
    ( test_forallSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import Data.Reflection
       ( Given, give )

import           Kore.AST.Pure
import           Kore.ASTUtils.SmartConstructors
                 ( mkAnd, mkApp, mkCeil, mkEquals, mkForall, mkVar )
import           Kore.IndexedModule.MetadataTools
                 ( SymbolOrAliasSorts )
import           Kore.Predicate.Predicate
                 ( makeCeilPredicate, makeEqualsPredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( bottom, top )
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern, OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import qualified Kore.Step.Simplification.Forall as Forall
                 ( makeEvaluate, simplify )
import qualified Kore.Unification.Substitution as Substitution

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeSymbolOrAliasSorts )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_forallSimplification :: [TestTree]
test_forallSimplification = give mockSymbolOrAliasSorts
    [ testCase "Forall - or distribution"
        -- forall(a or b) = forall(a) or forall(b)
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ Predicated
                    { term = mkForall Mock.x something1OfX
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                , Predicated
                    { term = mkForall Mock.x something2OfX
                    , predicate = makeTruePredicate
                    , substitution = mempty
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
            Predicated
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
                , substitution = mempty
                }
            (makeEvaluate
                Mock.x
                Predicated
                    { term = mkApp Mock.fSymbol [mkVar Mock.x]
                    , predicate = makeCeilPredicate (Mock.h (mkVar Mock.x))
                    , substitution =
                        Substitution.wrap [(Mock.x, gOfA), (Mock.y, fOfA)]
                    }
            )
        )
    , testCase "forall disappears if variable not used"
        -- forall x . (t and p and s)
        (assertEqualWithExplanation "forall with substitution"
            Predicated
                { term =
                    mkForall Mock.x (mkAnd fOfA (mkCeil gOfA))
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            (makeEvaluate
                Mock.x
                Predicated
                    { term = fOfA
                    , predicate = makeCeilPredicate gOfA
                    , substitution = mempty
                    }
            )
        )
    , testCase "forall applied on term if not used elsewhere"
        -- forall x . (t(x) and p and s)
        (assertEqualWithExplanation "forall on term"
            Predicated
                { term = mkForall Mock.x (mkAnd fOfX (mkCeil gOfA))
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            (makeEvaluate
                Mock.x
                Predicated
                    { term = fOfX
                    , predicate = makeCeilPredicate gOfA
                    , substitution = mempty
                    }
            )
        )
    , testCase "forall applied on predicate if not used elsewhere"
        -- forall x . (t and p(x) and s)
        --    = t and (forall x . p(x)) and s
        --    if t, s do not depend on x.
        (assertEqualWithExplanation "forall on predicate"
            Predicated
                { term = mkForall Mock.x (mkAnd fOfA (mkCeil fOfX))
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            (makeEvaluate
                Mock.x
                Predicated
                    { term = fOfA
                    , predicate = makeCeilPredicate fOfX
                    , substitution = mempty
                    }
            )
        )
    , testCase "forall moves substitution above"
        -- forall x . (t(x) and p(x) and s)
        (assertEqualWithExplanation "forall moves substitution"
            Predicated
                { term =
                    mkForall Mock.x
                        (mkAnd
                            (mkAnd fOfX (mkEquals fOfX gOfA))
                            (mkEquals (mkVar Mock.y) hOfA)
                        )
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            (makeEvaluate
                Mock.x
                Predicated
                    { term = fOfX
                    , predicate = makeEqualsPredicate fOfX gOfA
                    , substitution = Substitution.wrap [(Mock.y, hOfA)]
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
    fOfA = give mockSymbolOrAliasSorts $ Mock.f Mock.a
    fOfX = give mockSymbolOrAliasSorts $ Mock.f (mkVar Mock.x)
    gOfA = give mockSymbolOrAliasSorts $ Mock.g Mock.a
    hOfA = give mockSymbolOrAliasSorts $ Mock.h Mock.a
    something1OfX = give mockSymbolOrAliasSorts $ Mock.plain10 (mkVar Mock.x)
    something2OfX = give mockSymbolOrAliasSorts $ Mock.plain11 (mkVar Mock.x)
    something1OfXExpanded = Predicated
        { term = something1OfX
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    something2OfXExpanded = Predicated
        { term = something2OfX
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    mockSymbolOrAliasSorts = Mock.makeSymbolOrAliasSorts Mock.symbolOrAliasSortsMapping

makeForall
    :: Ord (variable Object)
    => variable Object
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
        , Given (SymbolOrAliasSorts level)
        )
    => Forall level Variable (CommonOrOfExpandedPattern level)
    -> CommonOrOfExpandedPattern level
evaluate forall =
    fst $ Forall.simplify forall

makeEvaluate
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        )
    => Variable level
    -> CommonExpandedPattern level
    -> CommonExpandedPattern level
makeEvaluate variable child =
    fst $ Forall.makeEvaluate variable child
