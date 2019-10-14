module Test.Kore.Step.Simplification.Exists
    ( test_makeEvaluate
    , test_simplify
    ) where

import Test.Tasty

import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
import Kore.Predicate.Predicate
    ( makeAndPredicate
    , makeCeilPredicate
    , makeEqualsPredicate
    , makeExistsPredicate
    , makeTruePredicate
    )
import qualified Kore.Predicate.Predicate as Predicate
import qualified Kore.Step.Simplification.Exists as Exists
import qualified Kore.Unification.Substitution as Substitution
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext

test_simplify :: [TestTree]
test_simplify =
    [ [plain10, plain11] `simplifiesTo` [plain10', plain11']
        $ "\\or distribution"
    , [top]              `simplifiesTo` [top]
        $ "\\top"
    , []                 `simplifiesTo` []
        $ "\\bottom"
    , [equals]           `simplifiesTo` [quantifyPredicate equals]
        $ "\\equals"
    , [substForX]        `simplifiesTo` [top]
        $ "discharge substitution"
    , [substToX]         `simplifiesTo` [top]
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
            { predicate =
                Predicate.makeEqualsPredicate
                    (Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.z))
                    (Mock.functional20 (mkElemVar Mock.y) (mkElemVar Mock.z))
            }
    quantifyPredicate predicated@Conditional { predicate } =
        predicated
            { predicate = Predicate.makeExistsPredicate Mock.x predicate }
    quantifySubstitution predicated@Conditional { predicate, substitution } =
        predicated
            { predicate =
                Predicate.makeAndPredicate predicate
                $ Predicate.makeExistsPredicate Mock.x
                $ Predicate.fromSubstitution substitution
            , substitution = mempty
            }
    substForX =
        (Pattern.topOf Mock.testSort)
            { substitution = Substitution.unsafeWrap
                [ ( ElemVar Mock.x
                  , Mock.sigma (mkElemVar Mock.y) (mkElemVar Mock.z))]
            }
    substToX =
        (Pattern.topOf Mock.testSort)
            { substitution =
                Substitution.unsafeWrap [(ElemVar Mock.y, mkElemVar Mock.x)] }
    substOfX =
        (Pattern.topOf Mock.testSort)
            { substitution = Substitution.unsafeWrap
                [ ( ElemVar Mock.y
                  , Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.z)
                  )
                ]
            }
    simplifiesTo
        :: HasCallStack
        => [Pattern Variable]
        -> [Pattern Variable]
        -> String
        -> TestTree
    simplifiesTo original expected message =
        testCase message $ do
            actual <- simplify (makeExists Mock.x original)
            assertEqual "expected simplification"
                (OrPattern.fromPatterns expected) actual

test_makeEvaluate :: [TestTree]
test_makeEvaluate =
    [ testGroup "Exists - Predicates"
        [ testCase "Top" $ do
            let expect = OrPattern.fromPatterns [ Pattern.top ]
            actual <- makeEvaluate Mock.x (Pattern.top :: Pattern Variable)
            assertEqual "" expect actual

        , testCase " Bottom" $ do
            let expect = OrPattern.fromPatterns []
            actual <- makeEvaluate Mock.x (Pattern.bottom :: Pattern Variable)
            assertEqual "" expect actual
        ]

    , testCase "exists applies substitution if possible" $ do
        -- exists x . (t(x) and p(x) and [x = alpha, others])
        --    = t(alpha) and p(alpha) and [others]
        let expect =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = Mock.f gOfA
                        , predicate =
                            makeCeilPredicate (Mock.h gOfA)
                        , substitution = Substitution.unsafeWrap
                            [(ElemVar Mock.y, fOfA)]
                        }
                    ]
        actual <-
            makeEvaluate
                Mock.x
                Conditional
                    { term = Mock.f (mkElemVar Mock.x)
                    , predicate = makeCeilPredicate (Mock.h (mkElemVar Mock.x))
                    , substitution =
                        Substitution.wrap
                            [(ElemVar Mock.x, gOfA), (ElemVar Mock.y, fOfA)]
                    }
        assertEqual "exists with substitution" expect actual

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
                    , substitution = Substitution.wrap [(ElemVar Mock.y, hOfA)]
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
                    , substitution = Substitution.wrap [(ElemVar Mock.x, gOfA)]
                    }
        assertEqual "exists reevaluates" expect actual
    , testCase "exists matches equality if result is top" $ do
        -- exists x . (f(x) = f(a))
        --    = top.s
        let expect = OrPattern.fromPatterns
                [ Conditional
                    { term = fOfA
                    , predicate = makeTruePredicate
                    , substitution = Substitution.wrap [(ElemVar Mock.y, fOfA)]
                    }
                ]
        actual <-
            makeEvaluate
                Mock.x
                Conditional
                    { term = fOfA
                    , predicate = makeEqualsPredicate fOfX (Mock.f Mock.a)
                    , substitution = Substitution.wrap [(ElemVar Mock.y, fOfA)]
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
                                (makeEqualsPredicate fOfX (Mock.f Mock.a))
                                (makeEqualsPredicate (mkElemVar Mock.y) fOfX)
                            )
                    , substitution = Substitution.wrap [(ElemVar Mock.z, fOfA)]
                    }
                ]
        actual <-
            makeEvaluate
                Mock.x
                Conditional
                    { term = fOfA
                    , predicate = makeEqualsPredicate fOfX (Mock.f Mock.a)
                    , substitution =
                        Substitution.wrap
                            [(ElemVar Mock.y, fOfX), (ElemVar Mock.z, fOfA)]
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
                    , substitution = Substitution.wrap [(ElemVar Mock.y, fOfA)]
                    }
    ]
  where
    fOfA = Mock.f Mock.a
    fOfX = Mock.f (mkElemVar Mock.x)
    gOfA = Mock.g Mock.a
    hOfA = Mock.h Mock.a

makeExists
    :: Ord variable
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
    :: Exists Sort Variable (OrPattern Variable)
    -> IO (OrPattern Variable)
simplify = runSimplifier Mock.env . Exists.simplify

makeEvaluate
    :: ElementVariable Variable
    -> Pattern Variable
    -> IO (OrPattern Variable)
makeEvaluate variable child =
    runSimplifier Mock.env $ Exists.makeEvaluate variable child
