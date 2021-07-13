module Test.Kore.Simplify.Forall (
    test_forallSimplification,
) where

import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    makeAndPredicate,
    makeCeilPredicate,
    makeEqualsPredicate,
    makeForallPredicate,
    makeTruePredicate,
 )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import qualified Kore.Simplify.Forall as Forall (
    makeEvaluate,
    simplify,
 )
import Prelude.Kore
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_forallSimplification :: [TestTree]
test_forallSimplification =
    [ testCase
        "Forall - or distribution"
        -- forall(a or b) = forall(a) or forall(b)
        ( assertEqual
            ""
            ( OrPattern.fromPatterns
                [ Conditional
                    { term = mkForall Mock.xConfig something1OfX
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                , Conditional
                    { term = mkForall Mock.xConfig something2OfX
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                ]
            )
            ( evaluate
                ( makeForall
                    Mock.xConfig
                    [something1OfXExpanded, something2OfXExpanded]
                )
            )
        )
    , testCase
        "Forall - bool operations"
        ( do
            -- forall(top) = top
            assertEqual
                "forall(top)"
                ( OrPattern.fromPatterns
                    [Pattern.top]
                )
                ( evaluate
                    ( makeForall
                        Mock.xConfig
                        [Pattern.top]
                    )
                )
            -- forall(bottom) = bottom
            assertEqual
                "forall(bottom)"
                ( OrPattern.fromPatterns
                    []
                )
                ( evaluate
                    ( makeForall
                        Mock.xConfig
                        []
                    )
                )
        )
    , testCase
        "expanded Forall - bool operations"
        ( do
            -- forall(top) = top
            assertEqual
                "forall(top)"
                Pattern.top
                ( makeEvaluate
                    Mock.xConfig
                    (Pattern.top :: Pattern RewritingVariableName)
                )
            -- forall(bottom) = bottom
            assertEqual
                "forall(bottom)"
                Pattern.bottom
                ( makeEvaluate
                    Mock.xConfig
                    (Pattern.bottom :: Pattern RewritingVariableName)
                )
        )
    , testCase
        "forall applies substitution if possible"
        -- forall x . (t(x) and p(x) and [x = alpha, others])
        ( assertEqual
            "forall with substitution"
            Conditional
                { term =
                    mkForall
                        Mock.xConfig
                        ( mkAnd
                            ( mkAnd
                                (Mock.f $ mkElemVar Mock.xConfig)
                                (mkCeil_ (Mock.h (mkElemVar Mock.xConfig)))
                            )
                            ( mkAnd
                                (mkEquals_ (mkElemVar Mock.xConfig) gOfA)
                                (mkEquals_ (mkElemVar Mock.yConfig) fOfA)
                            )
                        )
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            ( makeEvaluate
                Mock.xConfig
                Conditional
                    { term = Mock.f $ mkElemVar Mock.xConfig
                    , predicate =
                        makeCeilPredicate (Mock.h (mkElemVar Mock.xConfig))
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [ (inject Mock.xConfig, gOfA)
                                , (inject Mock.yConfig, fOfA)
                                ]
                    }
            )
        )
    , testCase
        "forall disappears if variable not used"
        -- forall x . (t and p and s)
        ( assertEqual
            "forall with substitution"
            Conditional
                { term = fOfA
                , predicate = makeCeilPredicate gOfA
                , substitution = mempty
                }
            ( makeEvaluate
                Mock.xConfig
                Conditional
                    { term = fOfA
                    , predicate = makeCeilPredicate gOfA
                    , substitution = mempty
                    }
            )
        )
    , testCase
        "forall applied when term contains variable, non-bool predicate"
        -- forall x . (t(x) and p and s)
        ( assertEqual
            "forall on term"
            Conditional
                { term = mkForall Mock.xConfig (mkAnd fOfX (mkCeil_ gOfA))
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            ( makeEvaluate
                Mock.xConfig
                Conditional
                    { term = fOfX
                    , predicate = makeCeilPredicate gOfA
                    , substitution = mempty
                    }
            )
        )
    , testCase
        "forall applied when term contains variable, bool predicate"
        -- forall x . (t(x) and top and top)
        ( assertEqual
            "forall on term bool predicate"
            Conditional
                { term = mkForall Mock.xConfig fOfX
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            ( makeEvaluate
                Mock.xConfig
                Conditional
                    { term = fOfX
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
            )
        )
    , testCase
        "forall applied when predicate contains variable, non-bool term"
        -- forall x . (t and p(x) and s)
        --    = (forall x . (t and p(x) and s)
        ( assertEqual
            "forall on predicate"
            Conditional
                { term =
                    mkForall
                        Mock.xConfig
                        ( mkAnd
                            ( mkAnd
                                fOfA
                                (mkCeil_ fOfX)
                            )
                            (mkEquals_ (mkElemVar Mock.yConfig) fOfA)
                        )
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            ( makeEvaluate
                Mock.xConfig
                Conditional
                    { term = fOfA
                    , predicate = makeCeilPredicate fOfX
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [(inject Mock.yConfig, fOfA)]
                    }
            )
        )
    , testCase
        "forall applied when predicate contains variable, bool term"
        -- forall x . (top and p(x) and s)
        --    = top and (forall x . p(x) and s)
        ( assertEqual
            "forall on predicate"
            Conditional
                { term = mkTop_
                , predicate =
                    makeForallPredicate
                        Mock.xConfig
                        ( makeAndPredicate
                            (makeCeilPredicate fOfX)
                            (makeEqualsPredicate (mkElemVar Mock.yConfig) fOfA)
                        )
                , substitution = mempty
                }
            ( makeEvaluate
                Mock.xConfig
                Conditional
                    { term = mkTop_
                    , predicate = makeCeilPredicate fOfX
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [(inject Mock.yConfig, fOfA)]
                    }
            )
        )
    , testCase
        "forall moves substitution above"
        -- forall x . (t(x) and p(x) and s)
        ( assertEqual
            "forall moves substitution"
            Conditional
                { term =
                    mkForall
                        Mock.xConfig
                        ( mkAnd
                            (mkAnd fOfX (mkEquals_ fOfX gOfA))
                            (mkEquals_ (mkElemVar Mock.yConfig) hOfA)
                        )
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            ( makeEvaluate
                Mock.xConfig
                Conditional
                    { term = fOfX
                    , predicate = makeEqualsPredicate fOfX gOfA
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [(inject Mock.yConfig, hOfA)]
                    }
            )
        )
        {-
        Uncomment this if we ever decide to substitute + reevaluate in foralls
        , testCase "forall reevaluates"
            -- forall x . (top and (f(x) = f(g(a)) and [x=g(a)])
            --    = top.s
            (assertEqual "forall reevaluates"
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
    fOfX = Mock.f (mkElemVar Mock.xConfig)
    gOfA = Mock.g Mock.a
    hOfA = Mock.h Mock.a
    something1OfX = Mock.plain10 (mkElemVar Mock.xConfig)
    something2OfX = Mock.plain11 (mkElemVar Mock.xConfig)
    something1OfXExpanded =
        Conditional
            { term = something1OfX
            , predicate = makeTruePredicate
            , substitution = mempty
            }
    something2OfXExpanded =
        Conditional
            { term = something2OfX
            , predicate = makeTruePredicate
            , substitution = mempty
            }

makeForall ::
    ElementVariable RewritingVariableName ->
    [Pattern RewritingVariableName] ->
    Forall Sort RewritingVariableName (OrPattern RewritingVariableName)
makeForall variable patterns =
    Forall
        { forallSort = testSort
        , forallVariable = variable
        , forallChild = OrPattern.fromPatterns patterns
        }

testSort :: Sort
testSort = Mock.testSort

evaluate ::
    Forall Sort RewritingVariableName (OrPattern RewritingVariableName) ->
    OrPattern RewritingVariableName
evaluate = Forall.simplify

makeEvaluate ::
    ElementVariable RewritingVariableName ->
    Pattern RewritingVariableName ->
    Pattern RewritingVariableName
makeEvaluate = Forall.makeEvaluate
