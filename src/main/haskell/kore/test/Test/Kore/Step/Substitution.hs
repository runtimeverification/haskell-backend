module Test.Kore.Step.Substitution
    ( test_mergeAndNormalizeSubstitutions
    ) where

import Control.Monad.Except
import Data.Reflection
       ( give )
import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import           Kore.AST.Common
                 ( Variable )
import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.ASTUtils.SmartConstructors
                 ( mkVar )
import           Kore.Predicate.Predicate
                 ( makeCeilPredicate, makeEqualsPredicate, makeFalsePredicate,
                 makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( PredicateSubstitution, Predicated (..) )
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutionsExcept,
                 normalizePredicatedSubstitution )
import           Kore.Unification.Error
import           Kore.Unification.Unifier
                 ( UnificationSubstitution )
import qualified SMT

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools, makeSymbolOrAliasSorts )
import qualified Test.Kore.Step.MockSimplifiers as Mock
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_mergeAndNormalizeSubstitutions :: [TestTree]
test_mergeAndNormalizeSubstitutions = give mockSymbolOrAliasSorts
    [ testCase "Constructor normalization"
        -- [x=constructor(a)] + [x=constructor(a)]  === [x=constructor(a)]
        (assertEqual ""
            ( Right Predicated
                { term = ()
                , predicate = makeTruePredicate
                , substitution =
                    [   ( Mock.x
                        , Mock.constr10 Mock.a
                        )
                    ]
                }
            )
            ( normalize
                [   ( Mock.x
                    , Mock.constr10 Mock.a
                    )
                ]
                [   ( Mock.x
                    , Mock.constr10 Mock.a
                    )
                ]
            )
        )

    , testCase "Constructor normalization with variables"
        -- [x=constructor(y)] + [x=constructor(y)]  === [x=constructor(y)]
        (assertEqual ""
            ( Right Predicated
                { term = ()
                , predicate = makeTruePredicate
                , substitution =
                    [   ( Mock.x
                        , Mock.constr10 (mkVar Mock.y)
                        )
                    ]
                }
            )
            ( normalize
                [   ( Mock.x
                    , Mock.constr10 (mkVar Mock.y)
                    )
                ]
                [   ( Mock.x
                    , Mock.constr10 (mkVar Mock.y)
                    )
                ]
            )
        )

    , testCase "Double constructor is bottom"
        -- [x=constructor(a)] + [x=constructor(constructor(a))]  === bottom?
        (assertEqual ""
            ( Right Predicated
                { term = ()
                , predicate = makeFalsePredicate
                , substitution = []
                }
            )
            ( normalize
                [   ( Mock.x
                    , Mock.constr10 Mock.a
                    )
                ]
                [   ( Mock.x
                    , Mock.constr10 (Mock.constr10 Mock.a)
                    )
                ]
            )
        )

    , testCase "Double constructor is bottom with variables"
        -- [x=constructor(y)] + [x=constructor(constructor(y))]  === bottom?
        (assertEqual ""
            ( Left (UnificationError UnsupportedPatterns) )
            ( normalize
                [   ( Mock.x
                    , Mock.constr10 (mkVar Mock.y)
                    )
                ]
                [   ( Mock.x
                    , Mock.constr10 (Mock.constr10 (mkVar Mock.y))
                    )
                ]
            )
        )

    , testCase "Constructor and constructor of function"
        -- [x=constructor(a)] + [x=constructor(f(a))]
        (assertEqual ""
            ( Right Predicated
                { term = ()
                , predicate =  makeEqualsPredicate Mock.a (Mock.f Mock.a)
                , substitution =
                    [   ( Mock.x
                        , Mock.constr10 Mock.a
                        )
                    ]
                }
            )
            ( normalize
                [   ( Mock.x
                    , Mock.constr10 Mock.a
                    )
                ]
                [   ( Mock.x
                    , Mock.constr10 (Mock.f Mock.a)
                    )
                ]
            )
        )

    -- TODO(Vladimir): this should be fixed by making use of the predicate from
    -- `solveGroupSubstitutions`.
    , testCase "Constructor and constructor of function with variables"
        -- [x=constructor(y)] + [x=constructor(f(y))]
        (assertEqual ""
            ( Right Predicated
                { term = ()
                , predicate =
                    makeEqualsPredicate
                        ( mkVar Mock.y )
                        ( Mock.f (mkVar Mock.y) )
                , substitution =
                    [   ( Mock.x
                        , Mock.constr10 (Mock.f (mkVar Mock.y))
                        )
                    ]
                }
            )
            ( normalize
                [   ( Mock.x
                    , Mock.constr10 (mkVar Mock.y)
                    )
                ]
                [   ( Mock.x
                    , Mock.constr10 (Mock.f (mkVar Mock.y))
                    )
                ]
            )
        )

    , testCase "Constructor and constructor of functional symbol"
        -- [x=constructor(y)] + [x=constructor(functional(y))]
        (assertEqual ""
            ( Right Predicated
                { term = ()
                , predicate =
                    makeEqualsPredicate
                        ( mkVar Mock.y )
                        ( Mock.functional10 (mkVar Mock.y) )
                , substitution =
                    [   ( Mock.x
                        , Mock.constr10 (Mock.functional10 (mkVar Mock.y))
                        )
                    ]
                }
            )
            ( normalize
                [   ( Mock.x
                    , Mock.constr10 (mkVar Mock.y)
                    )
                ]
                [   ( Mock.x
                    , Mock.constr10 (Mock.functional10 (mkVar Mock.y))
                    )
                ]
            )
        )

    , testCase "Constructor circular dependency?"
        -- [x=y] + [y=constructor(x)]  === error
        (assertEqual ""
            ( Left $ UnificationError UnsupportedPatterns )
            ( normalize
                [   ( Mock.x
                    , mkVar Mock.y
                    )
                ]
                [   ( Mock.x
                    , Mock.constr10 (mkVar Mock.x)
                    )
                ]
            )
        )

    , testCase "Non-ctor circular dependency"
        -- [x=y] + [y=f(x)]  === error
        (assertEqual ""
            ( Left
                ( SubstitutionError
                    ( NonCtorCircularVariableDependency [ Mock.x, Mock.y ] )
                )
            )
            ( normalize
                [   ( Mock.x
                    , mkVar Mock.y
                    )
                ]
                [   ( Mock.y
                    , Mock.f (mkVar Mock.x)
                    )
                ]
            )
        )
    , testCase "Normalizes substitution"
        (assertEqualWithExplanation ""
            (Predicated
                { term = ()
                , predicate = makeTruePredicate
                , substitution =
                    [ (Mock.x, Mock.constr10 Mock.a)
                    , (Mock.y, Mock.a)
                    ]
                }
            )
            (normalizeWithPredicate
                Predicated
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution =
                        [ (Mock.x, Mock.constr10 Mock.a)
                        , (Mock.x, Mock.constr10 (mkVar Mock.y))
                        ]
                    }
            )
        )
    , testCase "Predicate from normalizing substitution"
        (assertEqualWithExplanation ""
            (Predicated
                { term = ()
                , predicate = makeEqualsPredicate Mock.cf Mock.cg
                , substitution =
                    [ (Mock.x, Mock.constr10 Mock.cf) ]
                }
            )
            (normalizeWithPredicate
                Predicated
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution =
                        [ (Mock.x, Mock.constr10 Mock.cf)
                        , (Mock.x, Mock.constr10 Mock.cg)
                        ]
                    }
            )
        )
    , testCase "Normalizes substitution and substitutes in predicate"
        (assertEqualWithExplanation ""
            (Predicated
                { term = ()
                , predicate = makeCeilPredicate (Mock.f Mock.a)
                , substitution =
                    [ (Mock.x, Mock.constr10 Mock.a)
                    , (Mock.y, Mock.a)
                    ]
                }
            )
            (normalizeWithPredicate
                Predicated
                    { term = ()
                    , predicate = makeCeilPredicate (Mock.f (mkVar Mock.y))
                    , substitution =
                        [ (Mock.x, Mock.constr10 Mock.a)
                        , (Mock.x, Mock.constr10 (mkVar Mock.y))
                        ]
                    }
            )
        )
    ]

  where
    mockSymbolOrAliasSorts =
        Mock.makeSymbolOrAliasSorts Mock.symbolOrAliasSortsMapping
    mockMetadataTools =
        Mock.makeMetadataTools
            mockSymbolOrAliasSorts
            Mock.attributesMapping
            Mock.headTypeMapping
            []
    normalize
        :: UnificationSubstitution Object Variable
        -> UnificationSubstitution Object Variable
        -> Either
            ( UnificationOrSubstitutionError Object Variable )
            ( PredicateSubstitution Object Variable )
    normalize s1 s2 =
        let
            result =
                SMT.unsafeRunSMT SMT.defaultConfig
                $ evalSimplifier
                $ runExceptT $ mergePredicatesAndSubstitutionsExcept
                    mockMetadataTools
                    (Mock.substitutionSimplifier mockMetadataTools)
                    []
                    [s1, s2]
        in
            case result of
                Left err -> Left err
                Right r -> Right (fst $ r)
    normalizeWithPredicate
        :: PredicateSubstitution Object Variable
        -> PredicateSubstitution Object Variable
    normalizeWithPredicate Predicated {predicate, substitution} =
        fst
        $ SMT.unsafeRunSMT SMT.defaultConfig
        $ evalSimplifier
        $ normalizePredicatedSubstitution
            mockMetadataTools
            (Mock.substitutionSimplifier mockMetadataTools)
            Predicated {term = (), predicate, substitution}
