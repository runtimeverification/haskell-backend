module Test.Kore.Simplify.Exists (
    test_makeEvaluate,
    test_simplify,
) where

import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional (
    Conditional (..),
 )
import qualified Kore.Internal.Conditional as Conditional (
    Conditional (..),
 )
import qualified Kore.Internal.SideCondition as SideCondition (
    top,
 )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import qualified Kore.Simplify.Exists as Exists
import Kore.Unparser
import Prelude.Kore
import qualified Pretty
import Test.Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Test.Kore.Internal.OrPattern as OrPattern
import Test.Kore.Internal.Pattern (
    Pattern,
 )
import qualified Test.Kore.Internal.Pattern as Pattern
import Test.Kore.Internal.Predicate as Predicate
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Kore.Simplify
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_simplify :: [TestTree]
test_simplify =
    [ [plain10, plain11] `simplifiesTo` [plain10', plain11'] $
        "\\or distribution"
    , [Pattern.top] `simplifiesTo` [Pattern.top] $
        "\\top"
    , [] `simplifiesTo` [] $
        "\\bottom"
    , [equals] `simplifiesTo` [quantifyPredicate equals] $
        "\\equals"
    , [substForX] `simplifiesTo` [Pattern.topOf Mock.testSort] $
        "discharge substitution"
    , [substForXWithCycleY]
        `simplifiesTo` [Pattern.fromCondition Mock.testSort predicateCycleY]
        $ "discharge substitution with cycle"
    , [substToX] `simplifiesTo` [Pattern.topOf Mock.testSort] $
        "discharge reverse substitution"
    , [substOfX] `simplifiesTo` [quantifySubstitution substOfX] $
        "substitution"
    ]
  where
    plain10 = pure $ Mock.plain10 (mkElemVar Mock.xConfig)
    plain11 = pure $ Mock.plain11 (mkElemVar Mock.xConfig)
    plain10' = mkExists Mock.xConfig <$> plain10
    plain11' = mkExists Mock.xConfig <$> plain11
    equals =
        (Pattern.topOf Mock.testSort)
            { Conditional.predicate =
                Predicate.makeEqualsPredicate
                    ( Mock.functional20
                        (mkElemVar Mock.yConfig)
                        (mkElemVar Mock.zConfig)
                    )
                    ( Mock.sigma
                        (mkElemVar Mock.xConfig)
                        (mkElemVar Mock.zConfig)
                    )
            }
    quantifyPredicate predicated@Conditional{predicate} =
        predicated
            { Conditional.predicate =
                Predicate.makeExistsPredicate Mock.xConfig predicate
            }
    quantifySubstitution predicated@Conditional{predicate, substitution} =
        predicated
            { Conditional.predicate =
                Predicate.makeAndPredicate predicate $
                    Predicate.makeExistsPredicate Mock.xConfig $
                        Substitution.toPredicate substitution
            , Conditional.substitution = mempty
            }
    substForX =
        (Pattern.topOf Mock.testSort)
            { Conditional.substitution =
                Substitution.unsafeWrap
                    [
                        ( inject Mock.xConfig
                        , Mock.sigma
                            (mkElemVar Mock.yConfig)
                            (mkElemVar Mock.zConfig)
                        )
                    ]
            }
    substToX =
        (Pattern.topOf Mock.testSort)
            { Conditional.substitution =
                Substitution.unsafeWrap
                    [(inject Mock.yConfig, mkElemVar Mock.xConfig)]
            }
    substOfX =
        (Pattern.topOf Mock.testSort)
            { Conditional.substitution =
                Substitution.unsafeWrap
                    [
                        ( inject Mock.yConfig
                        , Mock.sigma (mkElemVar Mock.xConfig) (mkElemVar Mock.zConfig)
                        )
                    ]
            }
    f = Mock.f
    y = mkElemVar Mock.yConfig
    predicateCycleY =
        Condition.fromPredicate $
            Predicate.makeAndPredicate
                (Predicate.makeCeilPredicate (f y))
                (Predicate.makeEqualsPredicate y (f y))
    substCycleY =
        mconcat
            [ Condition.fromPredicate (Predicate.makeCeilPredicate (f y))
            , ( Condition.fromSubstitution
                    . Substitution.wrap
                    . Substitution.mkUnwrappedSubstitution
              )
                [(inject Mock.yConfig, f y)]
            ]
    substForXWithCycleY = substForX `Pattern.andCondition` substCycleY

    simplifiesTo ::
        HasCallStack =>
        [Pattern RewritingVariableName] ->
        [Pattern RewritingVariableName] ->
        String ->
        TestTree
    simplifiesTo original expected testName =
        testCase testName $ do
            actual <- simplify (makeExists Mock.xConfig original)
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
    [ testGroup
        "Exists - Predicates"
        [ testCase "Top" $ do
            let expect = OrPattern.fromPatterns [Pattern.top]
            actual <-
                makeEvaluate
                    Mock.xConfig
                    (Pattern.top :: Pattern RewritingVariableName)
            assertEqual "" expect actual
        , testCase " Bottom" $ do
            let expect = OrPattern.fromPatterns []
            actual <-
                makeEvaluate
                    Mock.xConfig
                    (Pattern.bottom :: Pattern RewritingVariableName)
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
                        , substitution =
                            Substitution.unsafeWrap
                                [(inject Mock.yConfig, fOfA)]
                        }
                    ]
        actuals <-
            makeEvaluate
                Mock.xConfig
                Conditional
                    { term = Mock.f (mkElemVar Mock.xConfig)
                    , predicate =
                        makeCeilPredicate (Mock.h (mkElemVar Mock.xConfig))
                    , substitution =
                        Substitution.wrap . Substitution.mkUnwrappedSubstitution $
                            [ (inject Mock.xConfig, gOfA)
                            , (inject Mock.yConfig, fOfA)
                            ]
                    }
        Pattern.assertEquivalentPatterns expects actuals
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
                Mock.xConfig
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
                        { term = mkExists Mock.xConfig fOfX
                        , predicate = makeCeilPredicate gOfA
                        , substitution = mempty
                        }
                    ]
        actual <-
            makeEvaluate
                Mock.xConfig
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
                            makeExistsPredicate
                                Mock.xConfig
                                (makeCeilPredicate fOfX)
                        , substitution = mempty
                        }
                    ]
        actual <-
            makeEvaluate
                Mock.xConfig
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
                Mock.xConfig
                Conditional
                    { term = fOfX
                    , predicate = makeEqualsPredicate fOfX gOfA
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [(inject Mock.yConfig, hOfA)]
                    }
    , testCase "exists reevaluates" $ do
        -- exists x . (top and (f(x) = f(g(a)) and [x=g(a)])
        --    = top.s
        let expect = OrPattern.fromPatterns [Pattern.top]
        actual <-
            makeEvaluate
                Mock.xConfig
                Conditional
                    { term = mkTop_
                    , predicate = makeEqualsPredicate fOfX (Mock.f gOfA)
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [(inject Mock.xConfig, gOfA)]
                    }
        assertEqual "exists reevaluates" expect actual
    , testCase "exists matches equality if result is top" $ do
        -- exists x . (f(x) = f(a))
        --    = top.s
        let expect =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = fOfA
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.wrap $
                                Substitution.mkUnwrappedSubstitution
                                    [(inject Mock.yConfig, fOfA)]
                        }
                    ]
        actual <-
            makeEvaluate
                Mock.xConfig
                Conditional
                    { term = fOfA
                    , predicate = makeEqualsPredicate (Mock.f Mock.a) fOfX
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [(inject Mock.yConfig, fOfA)]
                    }
        assertEqual "exists matching" expect actual
    , testCase "exists does not match equality if free var in subst" $ do
        -- exists x . (f(x) = f(a)) and (y=f(x))
        --    = exists x . (f(x) = f(a)) and (y=f(x))
        let expect =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = fOfA
                        , predicate =
                            makeExistsPredicate
                                Mock.xConfig
                                ( makeAndPredicate
                                    (makeEqualsPredicate (Mock.f Mock.a) fOfX)
                                    ( makeEqualsPredicate
                                        (mkElemVar Mock.yConfig)
                                        fOfX
                                    )
                                )
                        , substitution =
                            Substitution.wrap $
                                Substitution.mkUnwrappedSubstitution
                                    [(inject Mock.zConfig, fOfA)]
                        }
                    ]
        actual <-
            makeEvaluate
                Mock.xConfig
                Conditional
                    { term = fOfA
                    , predicate = makeEqualsPredicate fOfX (Mock.f Mock.a)
                    , substitution =
                        Substitution.wrap . Substitution.mkUnwrappedSubstitution $
                            [ (inject Mock.yConfig, fOfX)
                            , (inject Mock.zConfig, fOfA)
                            ]
                    }
        assertEqual "exists matching" expect actual
    , testCase "exists does not match equality if free var in term" $
        -- error for exists x . (f(x) = f(a)) and (y=f(x))
        assertErrorIO (const (return ())) $
            makeEvaluate
                Mock.xConfig
                Conditional
                    { term = fOfX
                    , predicate = makeEqualsPredicate fOfX (Mock.f Mock.a)
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [(inject Mock.yConfig, fOfA)]
                    }
    ]
  where
    fOfA = Mock.f Mock.a
    fOfX = Mock.f (mkElemVar Mock.xConfig)
    gOfA = Mock.g Mock.a
    hOfA = Mock.h Mock.a

makeExists ::
    ElementVariable RewritingVariableName ->
    [Pattern RewritingVariableName] ->
    Exists Sort RewritingVariableName (OrPattern RewritingVariableName)
makeExists variable patterns =
    Exists
        { existsSort = testSort
        , existsVariable = variable
        , existsChild = OrPattern.fromPatterns patterns
        }

testSort :: Sort
testSort = Mock.testSort

simplify ::
    Exists Sort RewritingVariableName (OrPattern RewritingVariableName) ->
    IO (OrPattern RewritingVariableName)
simplify = runSimplifier Mock.env . Exists.simplify SideCondition.top

makeEvaluate ::
    ElementVariable RewritingVariableName ->
    Pattern RewritingVariableName ->
    IO (OrPattern RewritingVariableName)
makeEvaluate variable child =
    runSimplifier Mock.env $
        Exists.makeEvaluate SideCondition.top [variable] child
