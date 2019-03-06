module Test.Kore.Step.Simplification.Iff
    ( test_iffSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeCeilPredicate, makeEqualsPredicate,
                 makeIffPredicate, makeTruePredicate )
import           Kore.Step.Representation.ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern, Predicated (..) )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
                 ( bottom, top )
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( make )
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern, OrOfExpandedPattern )
import qualified Kore.Step.Simplification.Iff as Iff
                 ( makeEvaluate, simplify )
import qualified Kore.Unification.Substitution as Substitution

import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_iffSimplification :: [TestTree]
test_iffSimplification =
    [ testCase "Iff - bool operations"
        (do
            -- iff(top, top) = top
            assertEqualWithExplanation "iff(top,top)"
                (MultiOr.make
                    [ ExpandedPattern.top ]
                )
                (evaluate
                    (makeIff
                        [ExpandedPattern.top]
                        [ExpandedPattern.top]
                    )
                )
            -- iff(bottom,bottom) = top
            assertEqualWithExplanation "iff(bottom,bottom)"
                (MultiOr.make
                    [ ExpandedPattern.top ]
                )
                (evaluate
                    (makeIff
                        []
                        []
                    )
                )
            -- iff(top, bottom) = bottom
            assertEqualWithExplanation "iff(top,bottom)"
                (MultiOr.make
                    []
                )
                (evaluate
                    (makeIff
                        [ExpandedPattern.top]
                        []
                    )
                )
            -- iff(bottom, top) = bottom
            assertEqualWithExplanation "iff(bottom,top)"
                (MultiOr.make
                    []
                )
                (evaluate
                    (makeIff
                        []
                        [ExpandedPattern.top]
                    )
                )
        )
    , testCase "Iff - half bool"
        (do
            -- iff(top, p) = p
            assertEqualWithExplanation "iff(top,p)"
                (MultiOr.make
                    [ Predicated
                        { term = Mock.a
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
                )
                (evaluate
                    (makeIff
                        [ExpandedPattern.top]
                        [ Predicated
                            { term = Mock.a
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                        ]
                    )
                )
            -- iff(p, top) = p
            assertEqualWithExplanation "iff(p, top)"
                (MultiOr.make
                    [ Predicated
                        { term = Mock.a
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
                )
                (evaluate
                    (makeIff
                        [ Predicated
                            { term = Mock.a
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                        ]
                        [ExpandedPattern.top]
                    )
                )
            -- iff(bottom,p) = not p
            assertEqualWithExplanation "iff(bottom,p)"
                (MultiOr.make
                    [ Predicated
                        { term = mkNot Mock.a
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
                )
                (evaluate
                    (makeIff
                        []
                        [ Predicated
                            { term = Mock.a
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                        ]
                    )
                )
            -- iff(p,bottom) = not p
            assertEqualWithExplanation "iff(p,bottom)"
                (MultiOr.make
                    [ Predicated
                        { term = mkNot Mock.a
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
                )
                (evaluate
                    (makeIff
                        [ Predicated
                            { term = Mock.a
                            , predicate = makeTruePredicate
                            , substitution = mempty
                            }
                        ]
                        []
                    )
                )
        )
    , testCase "expanded Iff - bool operations"
        (do
            -- iff(top,top) = top
            assertEqualWithExplanation "iff(top,top)"
                (MultiOr.make
                    [ ExpandedPattern.top ]
                )
                (makeEvaluate
                    (ExpandedPattern.top :: CommonExpandedPattern Object)
                    (ExpandedPattern.top :: CommonExpandedPattern Object)
                )
            -- iff(bottom,bottom) = bottom
            assertEqualWithExplanation "iff(bottom,bottom)"
                (MultiOr.make
                    [ ExpandedPattern.top ]
                )
                (makeEvaluate
                    (ExpandedPattern.bottom :: CommonExpandedPattern Object)
                    (ExpandedPattern.bottom :: CommonExpandedPattern Object)
                )
            -- iff(top,bottom) = bottom
            assertEqualWithExplanation "iff(top,bottom)"
                (MultiOr.make
                    []
                )
                (makeEvaluate
                    (ExpandedPattern.top :: CommonExpandedPattern Object)
                    (ExpandedPattern.bottom :: CommonExpandedPattern Object)
                )
            -- iff(bottom,top) = bottom
            assertEqualWithExplanation "iff(bottom,top)"
                (MultiOr.make
                    []
                )
                (makeEvaluate
                    (ExpandedPattern.bottom :: CommonExpandedPattern Object)
                    (ExpandedPattern.top :: CommonExpandedPattern Object)
                )
        )
    , testCase "expanded Iff - half bool"
        (do
            -- iff(top, p) = p
            assertEqualWithExplanation "iff(top,p)"
                (MultiOr.make
                    [ Predicated
                        { term = Mock.a
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
                )
                (makeEvaluate
                    ExpandedPattern.top
                    Predicated
                        { term = Mock.a
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                )
            -- iff(p, top) = p
            assertEqualWithExplanation "iff(p, top)"
                (MultiOr.make
                    [ Predicated
                        { term = Mock.a
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
                )
                (makeEvaluate
                    Predicated
                        { term = Mock.a
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ExpandedPattern.top
                )
            -- iff(bottom,p) = not p
            assertEqualWithExplanation "iff(bottom,p)"
                (MultiOr.make
                    [ Predicated
                        { term = mkNot Mock.a
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
                )
                (makeEvaluate
                    ExpandedPattern.bottom
                    Predicated
                        { term = Mock.a
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                )
            -- iff(p,bottom) = not p
            assertEqualWithExplanation "iff(p,bottom)"
                (MultiOr.make
                    [ Predicated
                        { term = mkNot Mock.a
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
                )
                (makeEvaluate
                    Predicated
                        { term = Mock.a
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ExpandedPattern.bottom
                )
        )
    , testCase "iff with predicates and substitutions"
        -- iff(top and predicate1 and subst1, top and predicate2 and subst2)
        --     = top and (iff(predicate1 and subst1, predicate2 and subst2)
        (assertEqualWithExplanation "iff(top and predicate, top and predicate)"
            (MultiOr.make
                [ Predicated
                    { term = mkTop_
                    , predicate =
                        makeIffPredicate
                            (makeAndPredicate
                                (makeCeilPredicate Mock.cf)
                                (makeEqualsPredicate (mkVar Mock.x) Mock.a)
                            )
                            (makeAndPredicate
                                (makeCeilPredicate Mock.cg)
                                (makeEqualsPredicate (mkVar Mock.y) Mock.b)
                            )
                    , substitution = mempty
                    }
                ]
            )
            ( makeEvaluate
                Predicated
                    { term = mkTop_
                    , predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.wrap [(Mock.x, Mock.a)]
                    }
                Predicated
                    { term = mkTop_
                    , predicate = makeCeilPredicate Mock.cg
                    , substitution = Substitution.wrap [(Mock.y, Mock.b)]
                    }
            )
        )
    , testCase "iff with generic patterns"
        (assertEqualWithExplanation "iff(generic, generic)"
            (MultiOr.make
                [ Predicated
                    { term =
                        mkIff
                            (mkAnd
                                (mkAnd
                                    (Mock.f Mock.a)
                                    (mkCeil_ Mock.cf)
                                )
                                (mkEquals_ (mkVar Mock.x) Mock.a)
                            )
                            (mkAnd
                                (mkAnd
                                    (Mock.g Mock.b)
                                    (mkCeil_ Mock.cg)
                                )
                                (mkEquals_ (mkVar Mock.y) Mock.b)
                            )
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                ]
            )
            ( makeEvaluate
                Predicated
                    { term = Mock.f Mock.a
                    , predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.wrap [(Mock.x, Mock.a)]
                    }
                Predicated
                    { term = Mock.g Mock.b
                    , predicate = makeCeilPredicate Mock.cg
                    , substitution = Substitution.wrap [(Mock.y, Mock.b)]
                    }
            )
        )
    ]

makeIff
    :: (Ord (variable Object))
    => [ExpandedPattern Object variable]
    -> [ExpandedPattern Object variable]
    -> Iff Object (OrOfExpandedPattern Object variable)
makeIff first second =
    Iff
        { iffSort   = Mock.testSort
        , iffFirst  = MultiOr.make first
        , iffSecond = MultiOr.make second
        }

evaluate
    :: MetaOrObject level
    => Iff level (CommonOrOfExpandedPattern level)
    -> CommonOrOfExpandedPattern level
evaluate iff0 =
    case Iff.simplify iff0 of
        (result, _proof) -> result


makeEvaluate
    :: MetaOrObject level
    => CommonExpandedPattern level
    -> CommonExpandedPattern level
    -> CommonOrOfExpandedPattern level
makeEvaluate first second =
    case Iff.makeEvaluate first second of
        (result, _proof) -> result
