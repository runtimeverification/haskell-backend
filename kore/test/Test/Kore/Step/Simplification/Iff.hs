module Test.Kore.Step.Simplification.Iff
    ( test_simplify
    , test_makeEvaluate
    ) where

import Test.Tasty

import qualified Data.Function as Function

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
    , makeIffPredicate
    , makeTruePredicate
    )
import qualified Kore.Step.Simplification.Iff as Iff
    ( makeEvaluate
    , simplify
    )
import qualified Kore.Unification.Substitution as Substitution
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext
import qualified Test.Terse as Terse

test_simplify :: [TestTree]
test_simplify =
    [ testGroup "Boolean operations"
        (testSimplifyBoolean <$> [minBound..] <*> [minBound..])
    , testGroup "Half-Boolean operations"
        [ (top   , termA ) `becomes` [termA]     $ "iff(⊤, a) = a"
        , (termA , top   ) `becomes` [termA]     $ "iff(a, ⊤) = a"
        , (bottom, termA ) `becomes` [termNotA]  $ "iff(⊤, a) = ¬a"
        , (termA , bottom) `becomes` [termNotA]  $ "iff(a, ⊤) = ¬a"
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
    [ testGroup "Boolean operations"
        (testEvaluateBoolean <$> [minBound..] <*> [minBound..])
    , testGroup "Half-Boolean operations"
        [ (top   , termA ) `becomes` [termA]     $ "iff(⊤, a) = a"
        , (termA , top   ) `becomes` [termA]     $ "iff(a, ⊤) = a"
        , (bottom, termA ) `becomes` [termNotA]  $ "iff(⊤, a) = ¬a"
        , (termA , bottom) `becomes` [termNotA]  $ "iff(a, ⊤) = ¬a"
        ]
    , testCase "iff with predicates and substitutions"
        -- iff(top and predicate1 and subst1, top and predicate2 and subst2)
        --     = top and (iff(predicate1 and subst1, predicate2 and subst2)
        (assertEqual "iff(top and predicate, top and predicate)"
            (OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate =
                        makeIffPredicate
                            (makeAndPredicate
                                (makeCeilPredicate Mock.cf)
                                (makeEqualsPredicate (mkElemVar Mock.x) Mock.a)
                            )
                            (makeAndPredicate
                                (makeCeilPredicate Mock.cg)
                                (makeEqualsPredicate (mkElemVar Mock.y) Mock.b)
                            )
                    , substitution = mempty
                    }
                ]
            )
            ( makeEvaluate
                Conditional
                    { term = mkTop_
                    , predicate = makeCeilPredicate Mock.cf
                    , substitution =
                        Substitution.wrap [(ElemVar Mock.x, Mock.a)]
                    }
                Conditional
                    { term = mkTop_
                    , predicate = makeCeilPredicate Mock.cg
                    , substitution =
                        Substitution.wrap [(ElemVar Mock.y, Mock.b)]
                    }
            )
        )
    , testCase "iff with generic patterns"
        (assertEqual "iff(generic, generic)"
            (OrPattern.fromPatterns
                [ Conditional
                    { term =
                        mkIff
                            (mkAnd
                                (mkAnd
                                    (Mock.f Mock.a)
                                    (mkCeil_ Mock.cf)
                                )
                                (mkEquals_ (mkElemVar Mock.x) Mock.a)
                            )
                            (mkAnd
                                (mkAnd
                                    (Mock.g Mock.b)
                                    (mkCeil_ Mock.cg)
                                )
                                (mkEquals_ (mkElemVar Mock.y) Mock.b)
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
                        Substitution.wrap [(ElemVar Mock.x, Mock.a)]
                    }
                Conditional
                    { term = Mock.g Mock.b
                    , predicate = makeCeilPredicate Mock.cg
                    , substitution =
                        Substitution.wrap [(ElemVar Mock.y, Mock.b)]
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
        (Function.on makeEvaluate valueBool a b)
        ("iff(" ++ nameBool a ++ ", " ++ nameBool b ++ ")")
  where
    r = a == b

nameBool :: Bool -> String
nameBool x
    | x = "⊤"
    | otherwise = "⊥"

valueBool :: Bool -> Pattern Variable
valueBool x
    | x = Pattern.top
    | otherwise = Pattern.bottom

termA :: Pattern Variable
termA =
    Conditional
        { term = Mock.a
        , predicate = makeTruePredicate
        , substitution = mempty
        }

termNotA :: Pattern Variable
termNotA = mkNot <$> termA

makeIff
    :: (Ord variable)
    => [Pattern variable]
    -> [Pattern variable]
    -> Iff Sort (OrPattern variable)
makeIff first second =
    Iff
        { iffSort   = Mock.testSort
        , iffFirst  = OrPattern.fromPatterns first
        , iffSecond = OrPattern.fromPatterns second
        }

simplify
    :: Iff Sort (OrPattern Variable)
    -> IO (OrPattern Variable)
simplify = runSimplifier mockEnv . Iff.simplify
  where
    mockEnv = Mock.env

makeEvaluate
    :: Pattern Variable
    -> Pattern Variable
    -> OrPattern Variable
makeEvaluate = Iff.makeEvaluate
