module Test.Kore.Step.Simplification.Iff
    ( test_iffSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import Data.Reflection
       ( Given, give )

import           Kore.AST.Common
                 ( Iff (..) )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkAnd, mkCeil, mkEquals, mkIff, mkNot, mkTop, mkVar )
import           Kore.IndexedModule.MetadataTools
                 ( SymbolOrAliasSorts )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeCeilPredicate, makeEqualsPredicate,
                 makeIffPredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( bottom, top )
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern, OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import qualified Kore.Step.Simplification.Iff as Iff
                 ( makeEvaluate, simplify )

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeSymbolOrAliasSorts )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_iffSimplification :: [TestTree]
test_iffSimplification = give mockSymbolOrAliasSorts
    [ testCase "Iff - bool operations"
        (do
            -- iff(top, top) = top
            assertEqualWithExplanation "iff(top,top)"
                (OrOfExpandedPattern.make
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
                (OrOfExpandedPattern.make
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
                (OrOfExpandedPattern.make
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
                (OrOfExpandedPattern.make
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
                (OrOfExpandedPattern.make
                    [ Predicated
                        { term = Mock.a
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                    ]
                )
                (evaluate
                    (makeIff
                        [ExpandedPattern.top]
                        [ Predicated
                            { term = Mock.a
                            , predicate = makeTruePredicate
                            , substitution = []
                            }
                        ]
                    )
                )
            -- iff(p, top) = p
            assertEqualWithExplanation "iff(p, top)"
                (OrOfExpandedPattern.make
                    [ Predicated
                        { term = Mock.a
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                    ]
                )
                (evaluate
                    (makeIff
                        [ Predicated
                            { term = Mock.a
                            , predicate = makeTruePredicate
                            , substitution = []
                            }
                        ]
                        [ExpandedPattern.top]
                    )
                )
            -- iff(bottom,p) = not p
            assertEqualWithExplanation "iff(bottom,p)"
                (OrOfExpandedPattern.make
                    [ Predicated
                        { term = mkNot Mock.a
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                    ]
                )
                (evaluate
                    (makeIff
                        []
                        [ Predicated
                            { term = Mock.a
                            , predicate = makeTruePredicate
                            , substitution = []
                            }
                        ]
                    )
                )
            -- iff(p,bottom) = not p
            assertEqualWithExplanation "iff(p,bottom)"
                (OrOfExpandedPattern.make
                    [ Predicated
                        { term = mkNot Mock.a
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                    ]
                )
                (evaluate
                    (makeIff
                        [ Predicated
                            { term = Mock.a
                            , predicate = makeTruePredicate
                            , substitution = []
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
                (OrOfExpandedPattern.make
                    [ ExpandedPattern.top ]
                )
                (makeEvaluate
                    (ExpandedPattern.top :: CommonExpandedPattern Object)
                    (ExpandedPattern.top :: CommonExpandedPattern Object)
                )
            -- iff(bottom,bottom) = bottom
            assertEqualWithExplanation "iff(bottom,bottom)"
                (OrOfExpandedPattern.make
                    [ ExpandedPattern.top ]
                )
                (makeEvaluate
                    (ExpandedPattern.bottom :: CommonExpandedPattern Object)
                    (ExpandedPattern.bottom :: CommonExpandedPattern Object)
                )
            -- iff(top,bottom) = bottom
            assertEqualWithExplanation "iff(top,bottom)"
                (OrOfExpandedPattern.make
                    []
                )
                (makeEvaluate
                    (ExpandedPattern.top :: CommonExpandedPattern Object)
                    (ExpandedPattern.bottom :: CommonExpandedPattern Object)
                )
            -- iff(bottom,top) = bottom
            assertEqualWithExplanation "iff(bottom,top)"
                (OrOfExpandedPattern.make
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
                (OrOfExpandedPattern.make
                    [ Predicated
                        { term = Mock.a
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                    ]
                )
                (makeEvaluate
                    ExpandedPattern.top
                    Predicated
                        { term = Mock.a
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                )
            -- iff(p, top) = p
            assertEqualWithExplanation "iff(p, top)"
                (OrOfExpandedPattern.make
                    [ Predicated
                        { term = Mock.a
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                    ]
                )
                (makeEvaluate
                    Predicated
                        { term = Mock.a
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                    ExpandedPattern.top
                )
            -- iff(bottom,p) = not p
            assertEqualWithExplanation "iff(bottom,p)"
                (OrOfExpandedPattern.make
                    [ Predicated
                        { term = mkNot Mock.a
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                    ]
                )
                (makeEvaluate
                    ExpandedPattern.bottom
                    Predicated
                        { term = Mock.a
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                )
            -- iff(p,bottom) = not p
            assertEqualWithExplanation "iff(p,bottom)"
                (OrOfExpandedPattern.make
                    [ Predicated
                        { term = mkNot Mock.a
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                    ]
                )
                (makeEvaluate
                    Predicated
                        { term = Mock.a
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                    ExpandedPattern.bottom
                )
        )
    , testCase "iff with predicates and substitutions"
        -- iff(top and predicate1 and subst1, top and predicate2 and subst2)
        --     = top and (iff(predicate1 and subst1, predicate2 and subst2)
        (assertEqualWithExplanation "iff(top and predicate, top and predicate)"
            (OrOfExpandedPattern.make
                [ Predicated
                    { term = mkTop
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
                    , substitution = []
                    }
                ]
            )
            ( makeEvaluate
                Predicated
                    { term = mkTop
                    , predicate = makeCeilPredicate Mock.cf
                    , substitution = [(Mock.x, Mock.a)]
                    }
                Predicated
                    { term = mkTop
                    , predicate = makeCeilPredicate Mock.cg
                    , substitution = [(Mock.y, Mock.b)]
                    }
            )
        )
    , testCase "iff with generic patterns"
        (assertEqualWithExplanation "iff(generic, generic)"
            (OrOfExpandedPattern.make
                [ Predicated
                    { term =
                        mkIff
                            (mkAnd
                                (mkAnd
                                    (Mock.f Mock.a)
                                    (mkCeil Mock.cf)
                                )
                                (mkEquals (mkVar Mock.x) Mock.a)
                            )
                            (mkAnd
                                (mkAnd
                                    (Mock.g Mock.b)
                                    (mkCeil Mock.cg)
                                )
                                (mkEquals (mkVar Mock.y) Mock.b)
                            )
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ]
            )
            ( makeEvaluate
                Predicated
                    { term = Mock.f Mock.a
                    , predicate = makeCeilPredicate Mock.cf
                    , substitution = [(Mock.x, Mock.a)]
                    }
                Predicated
                    { term = Mock.g Mock.b
                    , predicate = makeCeilPredicate Mock.cg
                    , substitution = [(Mock.y, Mock.b)]
                    }
            )
        )
    ]
  where
    mockSymbolOrAliasSorts :: SymbolOrAliasSorts Object
    mockSymbolOrAliasSorts =
        Mock.makeSymbolOrAliasSorts Mock.symbolOrAliasSortsMapping

makeIff
    :: (Ord (variable Object))
    => [ExpandedPattern Object variable]
    -> [ExpandedPattern Object variable]
    -> Iff Object (OrOfExpandedPattern Object variable)
makeIff first second =
    Iff
        { iffSort   = Mock.testSort
        , iffFirst  = OrOfExpandedPattern.make first
        , iffSecond = OrOfExpandedPattern.make second
        }

evaluate
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        )
    => Iff level (CommonOrOfExpandedPattern level)
    -> CommonOrOfExpandedPattern level
evaluate iff0 =
    case Iff.simplify iff0 of
        (result, _proof) -> result


makeEvaluate
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        )
    => CommonExpandedPattern level
    -> CommonExpandedPattern level
    -> CommonOrOfExpandedPattern level
makeEvaluate first second =
    case Iff.makeEvaluate first second of
        (result, _proof) -> result
