module Test.Kore.Step.Simplification.Forall
    ( test_forallSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike
import           Kore.Predicate.Predicate
                 ( makeCeilPredicate, makeEqualsPredicate, makeTruePredicate )
import qualified Kore.Step.Simplification.Forall as Forall
                 ( makeEvaluate, simplify )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Variables.UnifiedVariable
                 ( UnifiedVariable (..) )

import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_forallSimplification :: [TestTree]
test_forallSimplification =
    [ testCase "Forall - or distribution"
        -- forall(a or b) = forall(a) or forall(b)
        (assertEqualWithExplanation ""
            (OrPattern.fromPatterns
                [ Conditional
                    { term = mkForall Mock.x something1OfX
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                , Conditional
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
                (OrPattern.fromPatterns
                    [ Pattern.top ]
                )
                (evaluate
                    (makeForall
                        Mock.x
                        [Pattern.top]
                    )
                )
            -- forall(bottom) = bottom
            assertEqualWithExplanation "forall(bottom)"
                (OrPattern.fromPatterns
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
                Pattern.top
                (makeEvaluate
                    Mock.x
                    (Pattern.top :: Pattern Variable)
                )
            -- forall(bottom) = bottom
            assertEqualWithExplanation "forall(bottom)"
                Pattern.bottom
                (makeEvaluate
                    Mock.x
                    (Pattern.bottom :: Pattern Variable)
                )
        )
    , testCase "forall applies substitution if possible"
        -- forall x . (t(x) and p(x) and [x = alpha, others])
        (assertEqualWithExplanation "forall with substitution"
            Conditional
                { term =
                    mkForall Mock.x
                        (mkAnd
                            (mkAnd
                                (Mock.f $ mkElemVar Mock.x)
                                (mkCeil_ (Mock.h (mkElemVar Mock.x)))
                            )
                            (mkAnd
                                (mkEquals_ (mkElemVar Mock.x) gOfA)
                                (mkEquals_ (mkElemVar Mock.y) fOfA)
                            )
                        )
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            (makeEvaluate
                Mock.x
                Conditional
                    { term = Mock.f $ mkElemVar Mock.x
                    , predicate = makeCeilPredicate (Mock.h (mkElemVar Mock.x))
                    , substitution =
                        Substitution.wrap [(ElemVar Mock.x, gOfA), (ElemVar Mock.y, fOfA)]
                    }
            )
        )
    , testCase "forall disappears if variable not used"
        -- forall x . (t and p and s)
        (assertEqualWithExplanation "forall with substitution"
            Conditional
                { term =
                    mkForall Mock.x (mkAnd fOfA (mkCeil_ gOfA))
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            (makeEvaluate
                Mock.x
                Conditional
                    { term = fOfA
                    , predicate = makeCeilPredicate gOfA
                    , substitution = mempty
                    }
            )
        )
    , testCase "forall applied on term if not used elsewhere"
        -- forall x . (t(x) and p and s)
        (assertEqualWithExplanation "forall on term"
            Conditional
                { term = mkForall Mock.x (mkAnd fOfX (mkCeil_ gOfA))
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            (makeEvaluate
                Mock.x
                Conditional
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
            Conditional
                { term = mkForall Mock.x (mkAnd fOfA (mkCeil_ fOfX))
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            (makeEvaluate
                Mock.x
                Conditional
                    { term = fOfA
                    , predicate = makeCeilPredicate fOfX
                    , substitution = mempty
                    }
            )
        )
    , testCase "forall moves substitution above"
        -- forall x . (t(x) and p(x) and s)
        (assertEqualWithExplanation "forall moves substitution"
            Conditional
                { term =
                    mkForall Mock.x
                        (mkAnd
                            (mkAnd fOfX (mkEquals_ fOfX gOfA))
                            (mkEquals_ (mkElemVar Mock.y) hOfA)
                        )
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            (makeEvaluate
                Mock.x
                Conditional
                    { term = fOfX
                    , predicate = makeEqualsPredicate fOfX gOfA
                    , substitution = Substitution.wrap [(ElemVar Mock.y, hOfA)]
                    }
            )
        )
    {-
    Uncomment this if we ever decide to substitute + reevaluate in foralls
    , testCase "forall reevaluates"
        -- forall x . (top and (f(x) = f(g(a)) and [x=g(a)])
        --    = top.s
        (assertEqualWithExplanation "forall reevaluates"
            Pattern.top
            (makeEvaluate
                Mock.x
                Pattern
                    { term = mkTop_
                    , predicate = makeEqualsPredicate fOfX (Mock.f gOfA)
                    , substitution = [(Mock.x, gOfA)]
                    }
            )
        )
        -}
    ]
  where
    fOfA = Mock.f Mock.a
    fOfX = Mock.f (mkElemVar Mock.x)
    gOfA = Mock.g Mock.a
    hOfA = Mock.h Mock.a
    something1OfX = Mock.plain10 (mkElemVar Mock.x)
    something2OfX = Mock.plain11 (mkElemVar Mock.x)
    something1OfXExpanded = Conditional
        { term = something1OfX
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    something2OfXExpanded = Conditional
        { term = something2OfX
        , predicate = makeTruePredicate
        , substitution = mempty
        }

makeForall
    :: Ord variable
    => ElementVariable variable
    -> [Pattern variable]
    -> Forall Sort variable (OrPattern variable)
makeForall variable patterns =
    Forall
        { forallSort = testSort
        , forallVariable  = variable
        , forallChild       = OrPattern.fromPatterns patterns
        }

testSort :: Sort
testSort = Mock.testSort

evaluate :: Forall Sort Variable (OrPattern Variable) -> OrPattern Variable
evaluate = Forall.simplify

makeEvaluate :: ElementVariable Variable -> Pattern Variable -> Pattern Variable
makeEvaluate = Forall.makeEvaluate
