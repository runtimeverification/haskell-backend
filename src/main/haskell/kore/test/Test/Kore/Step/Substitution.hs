module Test.Kore.Step.Substitution
    ( test_mergeAndNormalizeSubstitutions
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase, assertEqual )

import           Data.Reflection
                 ( give )

import           Kore.AST.Common
                 ( Variable )
import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.ASTUtils.SmartConstructors
                 ( mkVar )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( PredicateSubstitution (..) )
import           Kore.Step.Substitution
                 ( mergeAndNormalizeSubstitutions )
import           Kore.Unification.Error
import           Kore.Unification.Unifier
                 ( UnificationSubstitution )
import           Kore.Variables.Fresh.IntCounter
                 ( runIntCounter )

import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools, makeSortTools )
import qualified Test.Kore.Step.MockSymbols as Mock

test_mergeAndNormalizeSubstitutions :: [TestTree]
test_mergeAndNormalizeSubstitutions = give mockSortTools
    [ testCase "Constructor normalization"
        -- [x=constructor(a)] + [x=constructor(a)]  === [x=constructor(a, a)]
        -- TODO(Vladimir) the result is x=constructor(a) instead of x=(constructor(a,a))
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
    , testCase "Double constructor is bottom"
        -- [x=constructor(a)] + [x=constructor(constructor(a))]  === bottom?
        -- TODO(Vladimir) the result is error instead of bottom
        (assertEqual ""
            ( Left
                ( UnificationError
                    ( PatternClash
                        ( HeadClash Mock.aSymbol )
                        ( HeadClash Mock.constr10Symbol )
                    )
                )
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
    , testCase "Constructor and constructor of function errors"
        -- [x=constructor(a)] + [x=constructor(f(a))]  === error
        (assertEqual ""
            ( Left (UnificationError (NonConstructorHead Mock.fSymbol)) )
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
    , testCase "Constructor circular dependency?"
        -- [a=b] + [b=constructor(a)]  === bottom
        -- TODO(Vladimir) the result is error instead of bottom
        (assertEqual ""
            ( Left
                ( SubstitutionError
                    ( CtorCircularVariableDependency [ Mock.x, Mock.y ] )
                )
            )
            ( normalize
                [   ( Mock.x
                    , (mkVar Mock.y)
                    )
                ]
                [   ( Mock.y
                    , Mock.constr10 (mkVar Mock.x)
                    )
                ]
            )
        )
    , testCase "Non-ctor circular dependency"
        -- [a=b] + [b=f(a)]  === error
        (assertEqual ""
            ( Left
                ( SubstitutionError
                    ( NonCtorCircularVariableDependency [ Mock.x, Mock.y ] )
                )
            )
            ( normalize
                [   ( Mock.x
                    , (mkVar Mock.y)
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
    mockSortTools = Mock.makeSortTools Mock.sortToolsMapping
    mockMetadataTools =
        Mock.makeMetadataTools mockSortTools Mock.attributesMapping
    normalize
        :: UnificationSubstitution Object Variable
        -> UnificationSubstitution Object Variable
        -> Either
              ( UnificationOrSubstitutionError Object Variable )
              ( PredicateSubstitution Object Variable )
    normalize s1 s2 =
        case mergeAndNormalizeSubstitutions mockMetadataTools s1 s2 of
            Left e -> Left e
            Right res -> Right . fst . fst $ runIntCounter res 0
