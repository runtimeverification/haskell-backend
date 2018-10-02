module Test.Kore.Step.Substitution
    ( test_mergeAndNormalizeSubstitutions
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )
import Control.Monad.Except
import Control.Monad.Counter
       ( evalCounter )
import Data.Reflection
       ( give )

import           Kore.AST.Common
                 ( Variable )
import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.ASTUtils.SmartConstructors
                 ( mkVar )
import           Kore.Predicate.Predicate
                 ( makeEqualsPredicate, makeFalsePredicate, makeTruePredicate )
import           Kore.Step.PredicateSubstitution
                 ( PredicateSubstitution (PredicateSubstitution) )
import           Kore.Step.Substitution
                 ( mergeAndNormalizeSubstitutions )
import           Kore.Unification.Error
import           Kore.Unification.Unifier
                 ( UnificationSubstitution )

import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools, makeSymbolOrAliasSorts )
import qualified Test.Kore.Step.MockSymbols as Mock

test_mergeAndNormalizeSubstitutions :: [TestTree]
test_mergeAndNormalizeSubstitutions = give mockSymbolOrAliasSorts
    [ testCase "Constructor normalization"
        -- [x=constructor(a)] + [x=constructor(a)]  === [x=constructor(a)]
        (assertEqual ""
            ( Right
                ( PredicateSubstitution
                    makeTruePredicate
                    [   ( Mock.x
                        , Mock.constr10 Mock.a
                        )
                    ]
                )
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
            ( Right
                ( PredicateSubstitution
                    makeTruePredicate
                    [   ( Mock.x
                        , Mock.constr10 (mkVar Mock.y)
                        )
                    ]
                )
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
            ( Right $ PredicateSubstitution makeFalsePredicate [] )
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
            ( Right
                ( PredicateSubstitution
                    ( makeEqualsPredicate Mock.a (Mock.f Mock.a) )
                    [   ( Mock.x
                        , Mock.constr10 Mock.a
                        )
                    ]
                )
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
            ( Right
                ( PredicateSubstitution
                    ( makeEqualsPredicate
                        ( mkVar Mock.y )
                        ( Mock.f (mkVar Mock.y) )
                    )
                    [   ( Mock.x
                        , Mock.constr10 (Mock.f (mkVar Mock.y))
                        )
                    ]
                )
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
            ( Right
                ( PredicateSubstitution
                    ( makeEqualsPredicate
                          ( mkVar Mock.y )
                          ( Mock.functional10 (mkVar Mock.y) )
                    )
                    [   ( Mock.x
                        , Mock.constr10 (Mock.functional10 (mkVar Mock.y))
                        )
                    ]
                )
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
    ]

  where
    mockSymbolOrAliasSorts = Mock.makeSymbolOrAliasSorts Mock.symbolOrAliasSortsMapping
    mockMetadataTools =
        Mock.makeMetadataTools mockSymbolOrAliasSorts Mock.attributesMapping []
    normalize
        :: UnificationSubstitution Object Variable
        -> UnificationSubstitution Object Variable
        -> Either
              ( UnificationOrSubstitutionError Object Variable )
              ( PredicateSubstitution Object Variable )
    normalize s1 s2 =
        let
            result =
                evalCounter
                . runExceptT
                $ mergeAndNormalizeSubstitutions mockMetadataTools s1 s2
        in
            fmap fst result
