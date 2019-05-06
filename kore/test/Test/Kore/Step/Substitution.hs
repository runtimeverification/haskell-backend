module Test.Kore.Step.Substitution
    ( test_mergeAndNormalizeSubstitutions
    , test_normalize
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import qualified Data.Map as Map

import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Internal.MultiOr
                 ( MultiOr )
import qualified Kore.Internal.MultiOr as MultiOr
import           Kore.Internal.Predicate
                 ( Conditional (..), Predicate )
import qualified Kore.Internal.Predicate as Predicate
import           Kore.Internal.TermLike
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.Simplifier as Simplifier
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutionsExcept )
import qualified Kore.Step.Substitution as Substitution
import           Kore.Unification.Error
import qualified Kore.Unification.Substitution as Substitution
import qualified Kore.Unification.Unify as Monad.Unify
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
        actual <- normalize Predicate.bottomPredicate
        assertEqual "Expected empty result" expect actual
    , testCase "∃ y z. x = σ(y, z)" $ do
        let expect =
                Predicate.fromPredicate
                $ Syntax.Predicate.makeMultipleExists [Mock.y, Mock.z]
                $ Syntax.Predicate.makeEqualsPredicate
                    (mkVar Mock.x)
                    (Mock.sigma (mkVar Mock.y) (mkVar Mock.z))
        actual <- normalizeExcept expect
        assertEqual "Expected original result" (Right $ MultiOr.make [expect]) actual
    , testCase "¬∃ y z. x = σ(y, z)" $ do
        let expect =
                Predicate.fromPredicate
                $ Syntax.Predicate.makeNotPredicate
                $ Syntax.Predicate.makeMultipleExists [Mock.y, Mock.z]
                $ Syntax.Predicate.makeEqualsPredicate
                    (mkVar Mock.x)
                    (Mock.sigma (mkVar Mock.y) (mkVar Mock.z))
        actual <- normalizeExcept expect
        assertEqual "Expected original result" (Right $ MultiOr.make [expect]) actual
    ]

test_mergeAndNormalizeSubstitutions :: [TestTree]
test_mergeAndNormalizeSubstitutions =
    [ testCase "Constructor normalization"
        -- [x=constructor(a)] + [x=constructor(a)]  === [x=constructor(a)]
        $ do
            let expect =
                    Right $ Predicate.fromSubstitution $ Substitution.unsafeWrap
                        [ ( Mock.x , Mock.constr10 Mock.a ) ]
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
                    Right $ Predicate.fromSubstitution $ Substitution.unsafeWrap
                        [(Mock.x, Mock.constr10 (mkVar Mock.y))]
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
            let expect = Right Predicate.bottomPredicate
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
                    Right Conditional
                        { term = ()
                        , predicate =
                            Syntax.Predicate.makeEqualsPredicate
                                Mock.a
                                (Mock.f Mock.a)
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
                    [ Predicate.fromSubstitution $ Substitution.unsafeWrap
                        [ (Mock.x, Mock.constr10 Mock.a)
                        , (Mock.y, Mock.a)
                        ]
                    ]
            actual <-
                normalize
                $ Predicate.fromSubstitution $ Substitution.wrap
                    [ (Mock.x, Mock.constr10 Mock.a)
                    , (Mock.x, Mock.constr10 (mkVar Mock.y))
                    ]
            assertEqualWithExplanation "" expect actual

    , testCase "Predicate from normalizing substitution"
        $ do
            let expect =
                    [ Conditional
                        { term = ()
                        , predicate =
                            Syntax.Predicate.makeEqualsPredicate Mock.cf Mock.cg
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.x, Mock.constr10 Mock.cf) ]
                        }
                    ]
            actual <-
                normalize
                    Conditional
                        { term = ()
                        , predicate = Syntax.Predicate.makeTruePredicate
                        , substitution = Substitution.wrap
                            [ (Mock.x, Mock.constr10 Mock.cf)
                            , (Mock.x, Mock.constr10 Mock.cg)
                            ]
                        }
            assertEqualWithExplanation "" expect actual

    , testCase "Normalizes substitution and substitutes in predicate"
        $ do
            let expect =
                    [ Conditional
                        { term = ()
                        , predicate =
                            Syntax.Predicate.makeCeilPredicate
                            $ Mock.f Mock.a
                        , substitution = Substitution.unsafeWrap
                            [ (Mock.x, Mock.constr10 Mock.a)
                            , (Mock.y, Mock.a)
                            ]
                        }
                    ]
            actual <-
                normalize
                    Conditional
                        { term = ()
                        , predicate =
                            Syntax.Predicate.makeCeilPredicate
                            $ Mock.f (mkVar Mock.y)
                        , substitution = Substitution.wrap
                            [ (Mock.x, Mock.constr10 Mock.a)
                            , (Mock.x, Mock.constr10 (mkVar Mock.y))
                            ]
                        }
            assertEqualWithExplanation "" expect actual
    ]

mockMetadataTools :: SmtMetadataTools StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools
        Mock.attributesMapping
        Mock.headTypeMapping
        Mock.sortAttributesMapping
        Mock.subsorts
        Mock.headSortsMapping
        Mock.smtDeclarations

merge
    :: [(Variable, TermLike Variable)]
    -> [(Variable, TermLike Variable)]
    -> IO
        (Either
            ( UnificationOrSubstitutionError Variable )
            ( Predicate Variable )
        )
merge s1 s2 =
    runSMT
    $ evalSimplifier emptyLogger
    $ Monad.Unify.runUnifier
    $ mergePredicatesAndSubstitutionsExcept
        mockMetadataTools
        (Mock.substitutionSimplifier mockMetadataTools)
        (Simplifier.create mockMetadataTools Map.empty)
        Map.empty
        []
        $ Substitution.wrap <$> [s1, s2]

normalize
    :: Conditional Variable term
    -> IO [Conditional Variable term]
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

normalizeExcept
    :: Conditional Variable ()
    -> IO (Either (UnificationOrSubstitutionError Variable) (MultiOr (Conditional Variable ())))
normalizeExcept predicated =
    runSMT
    $ evalSimplifier emptyLogger
    $ Monad.Unify.runUnifier
    $ fmap MultiOr.make
    $ gather
    $ Substitution.normalizeExcept
        mockMetadataTools
        (Mock.substitutionSimplifier mockMetadataTools)
        (Simplifier.create mockMetadataTools Map.empty)
        Map.empty
        predicated

-- | Run an 'SMT' computation with the default configuration.
runSMT :: SMT a -> IO a
runSMT = SMT.runSMT SMT.defaultConfig
