module Test.Kore.Step.Substitution
    ( test_mergeAndNormalizeSubstitutions
    , test_normalize
    ) where

import Test.Tasty

import qualified Data.Foldable as Foldable

import Kore.Internal.MultiOr
    ( MultiOr
    )
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.Predicate
    ( Conditional (..)
    , Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import qualified Kore.Step.Simplification.Predicate as Predicate
import qualified Kore.Step.Substitution as Substitution
import Kore.Unification.Error
import qualified Kore.Unification.Substitution as Substitution
import qualified Kore.Unification.Unify as Monad.Unify
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import qualified Test.Kore.Step.MockSymbols as Mock
import qualified Test.Kore.Step.Simplification as Test
import Test.Tasty.HUnit.Ext

test_normalize :: [TestTree]
test_normalize =
    [ testCase "predicate = \\bottom" $ do
        let expect = mempty
        actual <- normalize Predicate.bottomPredicate
        assertEqual "Expected empty result" expect actual
        assertNormalizedPredicatesMulti actual
    , testCase "∃ y z. x = σ(y, z)" $ do
        let expect = Predicate.fromPredicate existsPredicate
        actual <- normalizeExcept expect
        assertEqual
            "Expected original result"
            (Right $ MultiOr.make [expect])
            actual
        Foldable.traverse_ assertNormalizedPredicatesMulti actual
    , testCase "¬∃ y z. x = σ(y, z)" $ do
        let expect =
                Predicate.fromPredicate
                $ Syntax.Predicate.makeNotPredicate existsPredicate
        actual <- normalizeExcept expect
        assertEqual
            "Expected original result"
            (Right $ MultiOr.make [expect])
            actual
        Foldable.traverse_ assertNormalizedPredicatesMulti actual
    ]
  where
    existsPredicate =
        Syntax.Predicate.makeMultipleExists [Mock.y, Mock.z]
        $ Syntax.Predicate.makeEqualsPredicate
            (mkElemVar Mock.x)
            (Mock.sigma (mkElemVar Mock.y) (mkElemVar Mock.z))

test_mergeAndNormalizeSubstitutions :: [TestTree]
test_mergeAndNormalizeSubstitutions =
    [ testCase "Constructor normalization"
        -- [x=constructor(a)] + [x=constructor(a)]  === [x=constructor(a)]
        $ do
            let expect = Right
                    [ Predicate.fromSubstitution $ Substitution.unsafeWrap
                        [ ( ElemVar Mock.x , Mock.constr10 Mock.a ) ]
                    ]
            actual <-
                merge
                    [   ( ElemVar Mock.x
                        , Mock.constr10 Mock.a
                        )
                    ]
                    [   ( ElemVar Mock.x
                        , Mock.constr10 Mock.a
                        )
                    ]
            assertEqual "" expect actual
            assertNormalizedPredicates actual

    , testCase "Constructor normalization with variables"
        -- [x=constructor(y)] + [x=constructor(y)]  === [x=constructor(y)]
        $ do
            let expect = Right
                    [ Predicate.fromSubstitution $ Substitution.unsafeWrap
                        [(ElemVar Mock.x, Mock.constr10 (mkElemVar Mock.y))]
                    ]
            actual <-
                merge
                    [   ( ElemVar Mock.x
                        , Mock.constr10 (mkElemVar Mock.y)
                        )
                    ]
                    [   ( ElemVar Mock.x
                        , Mock.constr10 (mkElemVar Mock.y)
                        )
                    ]
            assertEqual "" expect actual
            assertNormalizedPredicates actual

    , testCase "Double constructor is bottom"
        -- [x=constructor(a)] + [x=constructor(constructor(a))]  === bottom?
        $ do
            let expect = Right []
            actual <-
                merge
                    [   ( ElemVar Mock.x
                        , Mock.constr10 Mock.a
                        )
                    ]
                    [   ( ElemVar Mock.x
                        , Mock.constr10 (Mock.constr10 Mock.a)
                        )
                    ]
            assertEqual "" expect actual
            assertNormalizedPredicates actual

    , testCase "Double constructor is bottom with variables"
        -- [x=constructor(y)] + [x=constructor(constructor(y))]  === bottom?
        $ do
            let expect = Left $ UnificationError $ unsupportedPatterns
                    "Unknown unification case."
                    (Mock.constr10 (mkElemVar Mock.y))
                    (mkElemVar Mock.y)
            actual <-
                merge
                    [   ( ElemVar Mock.x
                        , Mock.constr10 (mkElemVar Mock.y)
                        )
                    ]
                    [   ( ElemVar Mock.x
                        , Mock.constr10 (Mock.constr10 (mkElemVar Mock.y))
                        )
                    ]
            assertEqual "" expect actual
            assertNormalizedPredicates actual

    , testCase "Constructor and constructor of function"
        -- [x=constructor(a)] + [x=constructor(f(a))]
        $ do
            let expect =
                    Right
                        [ Conditional
                            { term = ()
                            , predicate =
                                Syntax.Predicate.makeEqualsPredicate
                                    Mock.a
                                    (Mock.f Mock.a)
                            , substitution = Substitution.unsafeWrap
                                [   ( ElemVar Mock.x
                                    , Mock.constr10 Mock.a
                                    )
                                ]
                            }
                        ]
            actual <-
                merge
                    [   ( ElemVar Mock.x
                        , Mock.constr10 Mock.a
                        )
                    ]
                    [   ( ElemVar Mock.x
                        , Mock.constr10 (Mock.f Mock.a)
                        )
                    ]
            assertEqual "" expect actual
            assertNormalizedPredicates actual

    , testCase "Constructor and constructor of function with variables"
        -- [x=constructor(y)] + [x=constructor(f(y))]
        $ do
            let
                expect =
                    Left $ SubstitutionError
                        (SimplifiableCycle [ElemVar Mock.y])
            actual <-
                merge
                    [   ( ElemVar Mock.x
                        , Mock.constr10 (mkElemVar Mock.y)
                        )
                    ]
                    [   ( ElemVar Mock.x
                        , Mock.constr10 (Mock.f (mkElemVar Mock.y))
                        )
                    ]
            assertEqual "" expect actual
            assertNormalizedPredicates actual

    , testCase "Constructor and constructor of functional symbol"
        -- [x=constructor(y)] + [x=constructor(functional(y))]
        $ do
            let
                expect =
                    Left $ SubstitutionError
                        (SimplifiableCycle [ElemVar Mock.y])
            actual <-
                merge
                    [   ( ElemVar Mock.x
                        , Mock.constr10 (mkElemVar Mock.y)
                        )
                    ]
                    [   ( ElemVar Mock.x
                        , Mock.constr10 (Mock.functional10 (mkElemVar Mock.y))
                        )
                    ]
            assertEqual "" expect actual
            assertNormalizedPredicates actual

    , testCase "Constructor circular dependency?"
        -- [x=y] + [y=constructor(x)]  === error
        $ do
            let expect = Left $ UnificationError $ unsupportedPatterns
                    "Unknown unification case."
                    (Mock.constr10 (mkElemVar Mock.x))
                    (mkElemVar Mock.y)
            actual <-
                merge
                    [   ( ElemVar Mock.x
                        , mkElemVar Mock.y
                        )
                    ]
                    [   ( ElemVar Mock.x
                        , Mock.constr10 (mkElemVar Mock.x)
                        )
                    ]
            assertEqual "" expect actual
            assertNormalizedPredicates actual

    , testCase "Non-ctor circular dependency"
        -- [x=y] + [y=f(x)]  === error
        $ do
            let expect =
                    Left
                    $ SubstitutionError
                    $ SimplifiableCycle
                        [ ElemVar Mock.x, ElemVar Mock.y ]
            actual <-
                merge
                    [   ( ElemVar Mock.x
                        , mkElemVar Mock.y
                        )
                    ]
                    [   ( ElemVar Mock.y
                        , Mock.f (mkElemVar Mock.x)
                        )
                    ]
            assertEqual "" expect actual
            assertNormalizedPredicates actual

    , testCase "Normalizes substitution"
        $ do
            let expect =
                    [ Predicate.fromSubstitution $ Substitution.unsafeWrap
                        [ (ElemVar Mock.x, Mock.constr10 Mock.a)
                        , (ElemVar Mock.y, Mock.a)
                        ]
                    ]
            actual <-
                normalize
                $ Predicate.fromSubstitution $ Substitution.wrap
                    [ (ElemVar Mock.x, Mock.constr10 Mock.a)
                    , (ElemVar Mock.x, Mock.constr10 (mkElemVar Mock.y))
                    ]
            assertEqual "" expect actual
            assertNormalizedPredicatesMulti actual

    , testCase "Predicate from normalizing substitution"
        $ do
            let expect =
                    [ Conditional
                        { term = ()
                        , predicate =
                            Syntax.Predicate.makeEqualsPredicate Mock.cf Mock.cg
                        , substitution = Substitution.unsafeWrap
                            [ (ElemVar Mock.x, Mock.constr10 Mock.cf) ]
                        }
                    ]
            actual <-
                normalize
                    Conditional
                        { term = ()
                        , predicate = Syntax.Predicate.makeTruePredicate
                        , substitution = Substitution.wrap
                            [ (ElemVar Mock.x, Mock.constr10 Mock.cf)
                            , (ElemVar Mock.x, Mock.constr10 Mock.cg)
                            ]
                        }
            assertEqual "" expect actual
            assertNormalizedPredicatesMulti actual

    , testCase "Normalizes substitution and substitutes in predicate"
        $ do
            let expect =
                    [ Conditional
                        { term = ()
                        , predicate =
                            Syntax.Predicate.makeCeilPredicate
                            $ Mock.f Mock.a
                        , substitution = Substitution.unsafeWrap
                            [ (ElemVar Mock.x, Mock.constr10 Mock.a)
                            , (ElemVar Mock.y, Mock.a)
                            ]
                        }
                    ]
            actual <-
                normalize
                    Conditional
                        { term = ()
                        , predicate =
                            Syntax.Predicate.makeCeilPredicate
                            $ Mock.f (mkElemVar Mock.y)
                        , substitution = Substitution.wrap
                            [ (ElemVar Mock.x, Mock.constr10 Mock.a)
                            , (ElemVar Mock.x, Mock.constr10 (mkElemVar Mock.y))
                            ]
                        }
            assertEqual "" expect actual
            assertNormalizedPredicatesMulti actual
    ]

merge
    :: [(UnifiedVariable Variable, TermLike Variable)]
    -> [(UnifiedVariable Variable, TermLike Variable)]
    -> IO (Either UnificationOrSubstitutionError [Predicate Variable])
merge s1 s2 =
    Test.runSimplifier mockEnv
    $ Monad.Unify.runUnifierT
    $ mergeSubstitutionsExcept $ Substitution.wrap <$> [s1, s2]
  where
    mergeSubstitutionsExcept =
        Substitution.normalizeExcept . Predicate.fromSubstitution . mconcat
    mockEnv = Mock.env

normalize :: Conditional Variable term -> IO [Conditional Variable term]
normalize = Test.runSimplifierBranch mockEnv . Predicate.simplifyPredicate
  where
    mockEnv = Mock.env

normalizeExcept
    :: Conditional Variable ()
    -> IO
        (Either
            UnificationOrSubstitutionError
            (MultiOr (Conditional Variable ()))
        )
normalizeExcept predicated =
    (fmap . fmap) MultiOr.make
    $ Test.runSimplifier mockEnv
    $ Monad.Unify.runUnifierT
    $ Substitution.normalizeExcept predicated
  where
    mockEnv = Mock.env

-- | Check that 'Predicate.substitution' is normalized for all arguments.
assertNormalizedPredicates :: Foldable f => f [Predicate Variable] -> Assertion
assertNormalizedPredicates =
    Foldable.traverse_ assertNormalizedPredicatesMulti

-- | Check that 'Predicate.substitution' is normalized for all arguments.
assertNormalizedPredicatesMulti
    :: Foldable f => f (Predicate Variable) -> Assertion
assertNormalizedPredicatesMulti =
    Foldable.traverse_ assertNormalizedPredicatesSingle

-- | Check that 'Predicate.substitution' is normalized for all arguments.
assertNormalizedPredicatesSingle :: Predicate Variable -> Assertion
assertNormalizedPredicatesSingle =
    assertBool "Substitution is normalized"
    . Substitution.isNormalized
    . Predicate.substitution
