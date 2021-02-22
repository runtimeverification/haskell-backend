module Test.Kore.Step.Simplification.Exists
    ( test_makeEvaluate
    , test_simplify
    ) where

import Prelude.Kore

import Test.Tasty

import Data.Align
    ( align
    )

import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional
    ( Conditional (..)
    )
import qualified Kore.Internal.Conditional as Conditional
    ( Conditional (..)
    )
import qualified Kore.Internal.MultiAnd as MultiAnd
import qualified Kore.Internal.SideCondition as SideCondition
    ( top
    )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
import qualified Kore.Step.Simplification.Exists as Exists
import Kore.Unparser
import qualified Pretty

import Test.Expect
import Test.Kore.Internal.OrPattern
    ( OrPattern
    , OrTestPattern
    )
import qualified Test.Kore.Internal.OrPattern as OrPattern
import Test.Kore.Internal.Pattern
    ( Pattern
    , TestPattern
    )
import qualified Test.Kore.Internal.Pattern as Pattern
import Test.Kore.Internal.Predicate as Predicate
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext

test_simplify :: [TestTree]
test_simplify =
    [ [plain10, plain11] `simplifiesTo` [plain10', plain11']
        $ "\\or distribution"
    , [Pattern.top]      `simplifiesTo` [Pattern.top]
        $ "\\top"
    , []                 `simplifiesTo` []
        $ "\\bottom"
    , [equals]           `simplifiesTo` [quantifyPredicate equals]
        $ "\\equals"
    , [substForX]        `simplifiesTo` [Pattern.topOf Mock.testSort]
        $ "discharge substitution"
    , [substForXWithCycleY]
        `simplifiesTo`
        [Pattern.fromCondition Mock.testSort predicateCycleY]
        $ "discharge substitution with cycle"
    , [substToX]         `simplifiesTo` [Pattern.topOf Mock.testSort]
        $ "discharge reverse substitution"
    , [substOfX]         `simplifiesTo` [quantifySubstitution substOfX]
        $ "substitution"
    ]
  where
    plain10 = pure $ Mock.plain10 (mkElemVar Mock.x)
    plain11 = pure $ Mock.plain11 (mkElemVar Mock.x)
    plain10' = mkExists Mock.x <$> plain10
    plain11' = mkExists Mock.x <$> plain11
    equals =
        (Pattern.topOf Mock.testSort)
            { Conditional.predicate =
                Predicate.makeEqualsPredicate
                    (Mock.functional20 (mkElemVar Mock.y) (mkElemVar Mock.z))
                    (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.z))
            }
    quantifyPredicate predicated@Conditional { predicate } =
        predicated
            { Conditional.predicate =
                Predicate.makeExistsPredicate Mock.x predicate
            }
    quantifySubstitution predicated@Conditional { predicate, substitution } =
        predicated
            { Conditional.predicate =
                Predicate.makeAndPredicate predicate
                $ Predicate.makeExistsPredicate Mock.x
                $ Substitution.toPredicate substitution
            , Conditional.substitution = mempty
            }
    substForX =
        (Pattern.topOf Mock.testSort)
            { Conditional.substitution = Substitution.unsafeWrap
                [   ( inject Mock.x
                    , Mock.sigma (mkElemVar Mock.y) (mkElemVar Mock.z)
                    )
                ]
            }
    substToX =
        (Pattern.topOf Mock.testSort)
            { Conditional.substitution =
                Substitution.unsafeWrap [(inject Mock.y, mkElemVar Mock.x)] }
    substOfX =
        (Pattern.topOf Mock.testSort)
            { Conditional.substitution = Substitution.unsafeWrap
                [ ( inject Mock.y
                  , Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.z)
                  )
                ]
            }
    f = Mock.f
    y = mkElemVar Mock.y
    predicateCycleY =
        Condition.fromPredicate
        $ Predicate.makeAndPredicate
            (Predicate.makeCeilPredicate (f y))
            (Predicate.makeEqualsPredicate y (f y))
    substCycleY =
        mconcat
            [ Condition.fromPredicate (Predicate.makeCeilPredicate (f y))
            , ( Condition.fromSubstitution
                . Substitution.wrap
                . Substitution.mkUnwrappedSubstitution
              )
                [(inject Mock.y, f y)]
            ]
    substForXWithCycleY = substForX `Pattern.andCondition` substCycleY

    simplifiesTo
        :: HasCallStack
        => [TestPattern]
        -> [TestPattern]
        -> String
        -> TestTree
    simplifiesTo original expected testName =
        testCase testName $ do
            actual <- simplify (makeExists Mock.x original)
            let message =
                    (show . Pretty.vsep)
                        [ "expected:"
                        , (Pretty.indent 4 . Pretty.vsep)
                            (unparse <$> expected)
                        , "actual:"
                        , (Pretty.indent 4 . Pretty.vsep)
                            (unparse <$> OrPattern.toPatterns actual)
                        ]
            assertEqual message expected (OrPattern.toPatterns actual)

test_makeEvaluate :: [TestTree]
test_makeEvaluate =
    [ testGroup "Exists - Predicates"
        [ testCase "Top" $ do
            let expect = OrPattern.fromPatterns [ Pattern.top ]
            actual <- makeEvaluate Mock.x (Pattern.top :: TestPattern)
            assertEqual "" expect actual

        , testCase " Bottom" $ do
            let expect = OrPattern.fromPatterns []
            actual <- makeEvaluate Mock.x (Pattern.bottom :: TestPattern)
            assertEqual "" expect actual
        ]

    , testCase "exists applies substitution if possible" $ do
        -- exists x . (t(x) and p(x) and [x = alpha, others])
        --    = t(alpha) and p(alpha) and [others]
        let expects =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = Mock.f gOfA
                        , predicate =
                            makeAndPredicate
                                (makeCeilPredicate gOfA)
                                (makeCeilPredicate (Mock.h gOfA))
                        , substitution = Substitution.unsafeWrap
                            [(inject Mock.y, fOfA)]
                        }
                    ]
        actuals <-
            makeEvaluate
                Mock.x
                Conditional
                    { term = Mock.f (mkElemVar Mock.x)
                    , predicate = makeCeilPredicate (Mock.h (mkElemVar Mock.x))
                    , substitution =
                        Substitution.wrap . Substitution.mkUnwrappedSubstitution
                            $ [(inject Mock.x, gOfA), (inject Mock.y, fOfA)]
                    }
        -- TODO: use this throughout the test code
        for_ (align (toList expects) (toList actuals)) $ \these -> do
            (expect, actual) <- expectThese these
            on (assertEqual "exists with substitution") term expect actual
            on (assertEqual "exists with substitution") (MultiAnd.fromPredicate . predicate) expect actual
            on (assertEqual "exists with substitution") substitution expect actual

    , testCase "exists disappears if variable not used" $ do
        -- exists x . (t and p and s)
        --    = t and p and s
        --    if t, p, s do not depend on x.
        let expect =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = fOfA
                        , predicate = makeCeilPredicate gOfA
                        , substitution = mempty
                        }
                    ]
        actual <-
            makeEvaluate
                Mock.x
                Conditional
                    { term = fOfA
                    , predicate = makeCeilPredicate gOfA
                    , substitution = mempty
                    }
        assertEqual "exists with substitution" expect actual

    , testCase "exists applied on term if not used elsewhere" $ do
        -- exists x . (t(x) and p and s)
        --    = (exists x . t(x)) and p and s
        --    if p, s do not depend on x.
        let expect =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = mkExists Mock.x fOfX
                        , predicate = makeCeilPredicate gOfA
                        , substitution = mempty
                        }
                    ]
        actual <-
            makeEvaluate
                Mock.x
                Conditional
                    { term = fOfX
                    , predicate = makeCeilPredicate gOfA
                    , substitution = mempty
                    }
        assertEqual "exists on term" expect actual

    , testCase "exists applied on predicate if not used elsewhere" $ do
        -- exists x . (t and p(x) and s)
        --    = t and (exists x . p(x)) and s
        --    if t, s do not depend on x.
        let expect =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = fOfA
                        , predicate =
                            makeExistsPredicate Mock.x (makeCeilPredicate fOfX)
                        , substitution = mempty
                        }
                    ]
        actual <-
            makeEvaluate
                Mock.x
                Conditional
                    { term = fOfA
                    , predicate = makeCeilPredicate fOfX
                    , substitution = mempty
                    }
        assertEqual "exists on predicate" expect actual

    , testCase "exists moves substitution above" $
        -- error for exists x . (t(x) and p(x) and s)
        assertErrorIO (const (return ())) $
            makeEvaluate
                Mock.x
                Conditional
                    { term = fOfX
                    , predicate = makeEqualsPredicate fOfX gOfA
                    , substitution =
                        Substitution.wrap
                        $ Substitution.mkUnwrappedSubstitution
                        [(inject Mock.y, hOfA)]
                    }

    , testCase "exists reevaluates" $ do
        -- exists x . (top and (f(x) = f(g(a)) and [x=g(a)])
        --    = top.s
        let expect = OrPattern.fromPatterns [ Pattern.top ]
        actual <-
            makeEvaluate
                Mock.x
                Conditional
                    { term = mkTop_
                    , predicate = makeEqualsPredicate fOfX (Mock.f gOfA)
                    , substitution =
                        Substitution.wrap
                        $ Substitution.mkUnwrappedSubstitution
                        [(inject Mock.x, gOfA)]
                    }
        assertEqual "exists reevaluates" expect actual
    , testCase "exists matches equality if result is top" $ do
        -- exists x . (f(x) = f(a))
        --    = top.s
        let expect = OrPattern.fromPatterns
                [ Conditional
                    { term = fOfA
                    , predicate = makeTruePredicate
                    , substitution =
                        Substitution.wrap
                        $ Substitution.mkUnwrappedSubstitution
                        [(inject Mock.y, fOfA)]
                    }
                ]
        actual <-
            makeEvaluate
                Mock.x
                Conditional
                    { term = fOfA
                    , predicate = makeEqualsPredicate (Mock.f Mock.a) fOfX
                    , substitution =
                        Substitution.wrap
                        $ Substitution.mkUnwrappedSubstitution
                        [(inject Mock.y, fOfA)]
                    }
        assertEqual "exists matching" expect actual
    , testCase "exists does not match equality if free var in subst" $ do
        -- exists x . (f(x) = f(a)) and (y=f(x))
        --    = exists x . (f(x) = f(a)) and (y=f(x))
        let expect = OrPattern.fromPatterns
                [ Conditional
                    { term = fOfA
                    , predicate =
                        makeExistsPredicate
                            Mock.x
                            (makeAndPredicate
                                (makeEqualsPredicate (Mock.f Mock.a) fOfX)
                                (makeEqualsPredicate (mkElemVar Mock.y) fOfX)
                            )
                    , substitution =
                        Substitution.wrap
                        $ Substitution.mkUnwrappedSubstitution
                        [(inject Mock.z, fOfA)]
                    }
                ]
        actual <-
            makeEvaluate
                Mock.x
                Conditional
                    { term = fOfA
                    , predicate = makeEqualsPredicate fOfX (Mock.f Mock.a)
                    , substitution =
                        Substitution.wrap . Substitution.mkUnwrappedSubstitution
                            $ [(inject Mock.y, fOfX), (inject Mock.z, fOfA)]
                    }
        assertEqual "exists matching" expect actual
    , testCase "exists does not match equality if free var in term" $
        -- error for exists x . (f(x) = f(a)) and (y=f(x))
        assertErrorIO (const (return ())) $
            makeEvaluate
                Mock.x
                Conditional
                    { term = fOfX
                    , predicate = makeEqualsPredicate fOfX (Mock.f Mock.a)
                    , substitution =
                        Substitution.wrap
                        $ Substitution.mkUnwrappedSubstitution
                        [(inject Mock.y, fOfA)]
                    }
    ]
  where
    fOfA = Mock.f Mock.a
    fOfX = Mock.f (mkElemVar Mock.x)
    gOfA = Mock.g Mock.a
    hOfA = Mock.h Mock.a

makeExists
    :: InternalVariable variable
    => ElementVariable variable
    -> [Pattern variable]
    -> Exists Sort variable (OrPattern variable)
makeExists variable patterns =
    Exists
        { existsSort = testSort
        , existsVariable = variable
        , existsChild = OrPattern.fromPatterns patterns
        }

testSort :: Sort
testSort = Mock.testSort

simplify
    :: Exists Sort VariableName OrTestPattern
    -> IO OrTestPattern
simplify = runSimplifier Mock.env . Exists.simplify SideCondition.top

makeEvaluate
    :: ElementVariable VariableName
    -> TestPattern
    -> IO OrTestPattern
makeEvaluate variable child =
    runSimplifier Mock.env
    $ Exists.makeEvaluate SideCondition.top [variable] child
