module Test.Kore.Step.Substitution
    ( test_mergeAndNormalizeSubstitutions
    , test_normalize
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import           Control.Monad.Except
import qualified Data.Map as Map

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Predicate.Predicate
                 ( makeCeilPredicate, makeEqualsPredicate, makeFalsePredicate,
                 makeTruePredicate )
import           Kore.Step.Pattern
                 ( StepPattern )
import           Kore.Step.Representation.MultiOr
                 ( MultiOr )
import qualified Kore.Step.Representation.MultiOr as MultiOr
import           Kore.Step.Representation.PredicateSubstitution
                 ( PredicateSubstitution, Predicated (..) )
import qualified Kore.Step.Representation.PredicateSubstitution as PredicateSubstitution
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.Simplifier as Simplifier
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutionsExcept )
import qualified Kore.Step.Substitution as Substitution
import           Kore.Unification.Error
import qualified Kore.Unification.Substitution as Substitution
import           SMT
                 ( SMT )
import qualified SMT

import           Test.Kore
import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools )
import qualified Test.Kore.Step.MockSimplifiers as Mock
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_normalize :: [TestTree]
test_normalize =
    [ testCase "predicate = \\bottom" $ do
        let expect = mempty
        actual <- normalize PredicateSubstitution.bottomPredicate
        assertEqual "Expected empty result" expect actual
    ]

test_mergeAndNormalizeSubstitutions :: [TestTree]
test_mergeAndNormalizeSubstitutions =
    [ testCase "Constructor normalization"
        -- [x=constructor(a)] + [x=constructor(a)]  === [x=constructor(a)]
        $ do
            let expect =
                    Right Predicated
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [   ( Mock.x
                                , Mock.constr10 Mock.a
                                )
                            ]
                        }
            actual <-
                merge
                    [   ( Mock.x
                        , Mock.constr10 Mock.a
                        )
                    ]
                    [   ( Mock.x
                        , Mock.constr10 Mock.a
                        )
                    ]
            assertEqual "" expect actual

    , testCase "Constructor normalization with variables"
        -- [x=constructor(y)] + [x=constructor(y)]  === [x=constructor(y)]
        $ do
            let expect =
                    Right Predicated
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.unsafeWrap
                            [   ( Mock.x
                                , Mock.constr10 (mkVar Mock.y)
                                )
                            ]
                        }
            actual <-
                merge
                    [   ( Mock.x
                        , Mock.constr10 (mkVar Mock.y)
                        )
                    ]
                    [   ( Mock.x
                        , Mock.constr10 (mkVar Mock.y)
                        )
                    ]
            assertEqual "" expect actual

    , testCase "Double constructor is bottom"
        -- [x=constructor(a)] + [x=constructor(constructor(a))]  === bottom?
        $ do
            let expect =
                    Right Predicated
                        { term = ()
                        , predicate = makeFalsePredicate
                        , substitution = mempty
                        }
            actual <-
                merge
                    [   ( Mock.x
                        , Mock.constr10 Mock.a
                        )
                    ]
                    [   ( Mock.x
                        , Mock.constr10 (Mock.constr10 Mock.a)
                        )
                    ]
            assertEqual "" expect actual

    , testCase "Double constructor is bottom with variables"
        -- [x=constructor(y)] + [x=constructor(constructor(y))]  === bottom?
        $ do
            let expect = Left (UnificationError UnsupportedPatterns)
            actual <-
                merge
                    [   ( Mock.x
                        , Mock.constr10 (mkVar Mock.y)
                        )
                    ]
                    [   ( Mock.x
                        , Mock.constr10 (Mock.constr10 (mkVar Mock.y))
                        )
                    ]
            assertEqual "" expect actual

    , testCase "Constructor and constructor of function"
        -- [x=constructor(a)] + [x=constructor(f(a))]
        $ do
            let expect =
                    Right Predicated
                        { term = ()
                        , predicate = makeEqualsPredicate Mock.a (Mock.f Mock.a)
                        , substitution = Substitution.unsafeWrap
                            [   ( Mock.x
                                , Mock.constr10 Mock.a
                                )
                            ]
                        }
            actual <-
                merge
                    [   ( Mock.x
                        , Mock.constr10 Mock.a
                        )
                    ]
                    [   ( Mock.x
                        , Mock.constr10 (Mock.f Mock.a)
                        )
                    ]
            assertEqual "" expect actual

    , testCase "Constructor and constructor of function with variables"
        -- [x=constructor(y)] + [x=constructor(f(y))]
        $ do
            let
                expect =
                    Left $ SubstitutionError
                        (NonCtorCircularVariableDependency [Mock.y])
            actual <-
                merge
                    [   ( Mock.x
                        , Mock.constr10 (mkVar Mock.y)
                        )
                    ]
                    [   ( Mock.x
                        , Mock.constr10 (Mock.f (mkVar Mock.y))
                        )
                    ]
            assertEqual "" expect actual

    , testCase "Constructor and constructor of functional symbol"
        -- [x=constructor(y)] + [x=constructor(functional(y))]
        $ do
            let
                expect =
                    Left $ SubstitutionError
                        (NonCtorCircularVariableDependency [Mock.y])
            actual <-
                merge
                    [   ( Mock.x
                        , Mock.constr10 (mkVar Mock.y)
                        )
                    ]
                    [   ( Mock.x
                        , Mock.constr10 (Mock.functional10 (mkVar Mock.y))
                        )
                    ]
            assertEqual "" expect actual

    , testCase "Constructor circular dependency?"
        -- [x=y] + [y=constructor(x)]  === error
        $ do
            let expect = Left $ UnificationError UnsupportedPatterns
            actual <-
                merge
                    [   ( Mock.x
                        , mkVar Mock.y
                        )
                    ]
                    [   ( Mock.x
                        , Mock.constr10 (mkVar Mock.x)
                        )
                    ]
            assertEqual "" expect actual

    , testCase "Non-ctor circular dependency"
        -- [x=y] + [y=f(x)]  === error
        $ do
            let expect =
                    Left
                    $ SubstitutionError
                    $ NonCtorCircularVariableDependency [ Mock.x, Mock.y ]
            actual <-
                merge
                    [   ( Mock.x
                        , mkVar Mock.y
                        )
                    ]
                    [   ( Mock.y
                        , Mock.f (mkVar Mock.x)
                        )
                    ]
            assertEqual "" expect actual

    , testCase "Normalizes substitution"
        $ do
            let expect =
                    MultiOr.make
                        [ Predicated
                            { term = ()
                            , predicate = makeTruePredicate
                            , substitution = Substitution.unsafeWrap
                                [ (Mock.x, Mock.constr10 Mock.a)
                                , (Mock.y, Mock.a)
                                ]
                            }
                        ]
            actual <-
                normalize
                    Predicated
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap
                            [ (Mock.x, Mock.constr10 Mock.a)
                            , (Mock.x, Mock.constr10 (mkVar Mock.y))
                            ]
                        }
            assertEqualWithExplanation "" expect actual

    , testCase "Predicate from normalizing substitution"
        $ do
            let expect =
                    MultiOr.make
                        [ Predicated
                            { term = ()
                            , predicate = makeEqualsPredicate Mock.cf Mock.cg
                            , substitution = Substitution.unsafeWrap
                                [ (Mock.x, Mock.constr10 Mock.cf) ]
                            }
                        ]
            actual <-
                normalize
                    Predicated
                        { term = ()
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap
                            [ (Mock.x, Mock.constr10 Mock.cf)
                            , (Mock.x, Mock.constr10 Mock.cg)
                            ]
                        }
            assertEqualWithExplanation "" expect actual

    , testCase "Normalizes substitution and substitutes in predicate"
        $ do
            let expect =
                    MultiOr.make
                        [ Predicated
                            { term = ()
                            , predicate = makeCeilPredicate (Mock.f Mock.a)
                            , substitution = Substitution.unsafeWrap
                                [ (Mock.x, Mock.constr10 Mock.a)
                                , (Mock.y, Mock.a)
                                ]
                            }
                        ]
            actual <-
                normalize
                    Predicated
                        { term = ()
                        , predicate = makeCeilPredicate (Mock.f (mkVar Mock.y))
                        , substitution = Substitution.wrap
                            [ (Mock.x, Mock.constr10 Mock.a)
                            , (Mock.x, Mock.constr10 (mkVar Mock.y))
                            ]
                        }
            assertEqualWithExplanation "" expect actual
    ]

mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools
        Mock.attributesMapping
        Mock.headTypeMapping
        Mock.sortAttributesMapping
        []

merge
    :: [(Variable Object, StepPattern Object Variable)]
    -> [(Variable Object, StepPattern Object Variable)]
    -> IO
        (Either
            ( UnificationOrSubstitutionError Object Variable )
            ( PredicateSubstitution Object Variable )
        )
merge s1 s2 =
    runSMT
    $ evalSimplifier emptyLogger
    $ runExceptT
    $ fmap fst
    $ mergePredicatesAndSubstitutionsExcept
        mockMetadataTools
        (Mock.substitutionSimplifier mockMetadataTools)
        (Simplifier.create mockMetadataTools Map.empty)
        Map.empty
        []
        $ Substitution.wrap <$> [s1, s2]

normalize
    :: Predicated Object Variable term
    -> IO (MultiOr (Predicated Object Variable term))
normalize predicated =
    runSMT
    $ evalSimplifier emptyLogger
    $ gather
    $ Substitution.normalize
        mockMetadataTools
        (Mock.substitutionSimplifier mockMetadataTools)
        (Simplifier.create mockMetadataTools Map.empty)
        Map.empty
        predicated

-- | Run an 'SMT' computation with the default configuration.
runSMT :: SMT a -> IO a
runSMT = SMT.runSMT SMT.defaultConfig
