module Test.Kore.Simplify.Iff (
    test_simplify,
    test_makeEvaluate,
) where

import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    makeAndPredicate,
    makeCeilPredicate,
    makeEqualsPredicate,
    makeIffPredicate,
    makeTruePredicate,
 )
import Kore.Internal.SideCondition qualified as SideCondition (
    top,
 )
import Kore.Internal.Substitution qualified as Substitution
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.Iff qualified as Iff (
    makeEvaluate,
    simplify,
 )
import Prelude.Kore
import Test.Kore.Rewrite.MockSymbols qualified as Mock
import Test.Kore.Simplify
import Test.Tasty
import Test.Tasty.HUnit.Ext
import Test.Terse qualified as Terse

test_simplify :: [TestTree]
test_simplify =
    [ testGroup
        "Boolean operations"
        (testSimplifyBoolean <$> [minBound ..] <*> [minBound ..])
    , testGroup
        "Half-Boolean operations"
        [ (topOf Mock.testSort, termA) `becomes` [termA] $ "iff(⊤, a) = a"
        , (termA, topOf Mock.testSort) `becomes` [termA] $ "iff(a, ⊤) = a"
        , (bottomOf Mock.testSort, termA) `becomes` [termNotA] $ "iff(⊤, a) = ¬a"
        , (termA, bottomOf Mock.testSort) `becomes` [termNotA] $ "iff(a, ⊤) = ¬a"
        ]
    ]
  where
    becomes (a, b) rs name =
        testCase name $ do
            let expect = OrPattern.fromPatterns rs
            actual <- simplify $ makeIff [a] [b]
            assertEqual "" expect actual

test_makeEvaluate :: [TestTree]
test_makeEvaluate =
    [ testGroup
        "Boolean operations"
        (testEvaluateBoolean <$> [minBound ..] <*> [minBound ..])
    , testGroup
        "Half-Boolean operations"
        [ (topOf Mock.testSort, termA) `becomes` [termA] $ "iff(⊤, a) = a"
        , (termA, topOf Mock.testSort) `becomes` [termA] $ "iff(a, ⊤) = a"
        , (bottomOf Mock.testSort, termA) `becomes` [termNotA] $ "iff(⊤, a) = ¬a"
        , (termA, bottomOf Mock.testSort) `becomes` [termNotA] $ "iff(a, ⊤) = ¬a"
        ]
    , testCase
        "iff with predicates and substitutions"
        -- iff(topOf Mock.testSort and predicate1 and subst1, topOf Mock.testSort and predicate2 and subst2)
        --     = topOf Mock.testSort and (iff(predicate1 and subst1, predicate2 and subst2)
        ( assertEqual
            "iff(topOf Mock.testSort and predicate, topOf Mock.testSort and predicate)"
            ( OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop Mock.testSort
                    , predicate =
                        makeIffPredicate
                            ( makeAndPredicate
                                (makeCeilPredicate Mock.cf)
                                ( makeEqualsPredicate
                                    (mkElemVar Mock.xConfig)
                                    Mock.a
                                )
                            )
                            ( makeAndPredicate
                                (makeCeilPredicate Mock.cg)
                                ( makeEqualsPredicate
                                    (mkElemVar Mock.yConfig)
                                    Mock.b
                                )
                            )
                    , substitution = mempty
                    }
                ]
            )
            ( makeEvaluate
                Conditional
                    { term = mkTop Mock.testSort
                    , predicate = makeCeilPredicate Mock.cf
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [(inject Mock.xConfig, Mock.a)]
                    }
                Conditional
                    { term = mkTop Mock.testSort
                    , predicate = makeCeilPredicate Mock.cg
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [(inject Mock.yConfig, Mock.b)]
                    }
            )
        )
    , testCase
        "iff with generic patterns"
        ( assertEqual
            "iff(generic, generic)"
            ( OrPattern.fromPatterns
                [ Conditional
                    { term =
                        mkIff
                            ( mkAnd
                                ( mkAnd
                                    (Mock.f Mock.a)
                                    (mkCeil Mock.testSort Mock.cf)
                                )
                                (mkEquals Mock.testSort (mkElemVar Mock.xConfig) Mock.a)
                            )
                            ( mkAnd
                                ( mkAnd
                                    (Mock.g Mock.b)
                                    (mkCeil Mock.testSort Mock.cg)
                                )
                                (mkEquals Mock.testSort (mkElemVar Mock.yConfig) Mock.b)
                            )
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                ]
            )
            ( makeEvaluate
                Conditional
                    { term = Mock.f Mock.a
                    , predicate = makeCeilPredicate Mock.cf
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [(inject Mock.xConfig, Mock.a)]
                    }
                Conditional
                    { term = Mock.g Mock.b
                    , predicate = makeCeilPredicate Mock.cg
                    , substitution =
                        Substitution.wrap $
                            Substitution.mkUnwrappedSubstitution
                                [(inject Mock.yConfig, Mock.b)]
                    }
            )
        )
    ]
  where
    becomes (a, b) rs =
        Terse.equals
            (makeEvaluate a b)
            (OrPattern.fromPatterns rs)

testSimplifyBoolean :: HasCallStack => Bool -> Bool -> TestTree
testSimplifyBoolean a b =
    testCase ("iff(" ++ nameBool a ++ ", " ++ nameBool b ++ ")") $ do
        actual <- simplify $ makeIff [valueBool a] [valueBool b]
        let expect = OrPattern.fromPatterns [valueBool r]
        assertEqual ("expected: " ++ nameBool r) expect actual
  where
    r = a == b

testEvaluateBoolean :: HasCallStack => Bool -> Bool -> TestTree
testEvaluateBoolean a b =
    Terse.equals
        (OrPattern.fromPatterns [valueBool r])
        (on makeEvaluate valueBool a b)
        ("iff(" ++ nameBool a ++ ", " ++ nameBool b ++ ")")
  where
    r = a == b

nameBool :: Bool -> String
nameBool x
    | x = "⊤"
    | otherwise = "⊥"

valueBool :: Bool -> Pattern RewritingVariableName
valueBool x
    | x = Pattern.topOf Mock.testSort
    | otherwise = Pattern.bottomOf Mock.testSort

termA :: Pattern RewritingVariableName
termA =
    Conditional
        { term = Mock.a
        , predicate = makeTruePredicate
        , substitution = mempty
        }

termNotA :: Pattern RewritingVariableName
termNotA = mkNot <$> termA

makeIff ::
    [Pattern RewritingVariableName] ->
    [Pattern RewritingVariableName] ->
    Iff Sort (OrPattern RewritingVariableName)
makeIff first second =
    Iff
        { iffSort = Mock.testSort
        , iffFirst = OrPattern.fromPatterns first
        , iffSecond = OrPattern.fromPatterns second
        }

simplify ::
    Iff Sort (OrPattern RewritingVariableName) ->
    IO (OrPattern RewritingVariableName)
simplify =
    testRunSimplifier mockEnv
        . Iff.simplify SideCondition.top
        . fmap simplifiedOrPattern
  where
    mockEnv = Mock.env

makeEvaluate ::
    Pattern RewritingVariableName ->
    Pattern RewritingVariableName ->
    OrPattern RewritingVariableName
makeEvaluate p1 p2 =
    Iff.makeEvaluate (simplifiedPattern p1) (simplifiedPattern p2)
