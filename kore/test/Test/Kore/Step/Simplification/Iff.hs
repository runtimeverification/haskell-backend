module Test.Kore.Step.Simplification.Iff
    ( test_simplify
    , test_makeEvaluate
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Function as Function
import qualified Data.Map.Strict as Map

import qualified Kore.Attribute.Symbol as Attribute
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Internal.TermLike
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeCeilPredicate, makeEqualsPredicate,
                 makeIffPredicate, makeTruePredicate )
import           Kore.Step.OrPattern
                 ( OrPattern )
import qualified Kore.Step.OrPattern as OrPattern
import           Kore.Step.Pattern as Pattern
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import qualified Kore.Step.Simplification.Iff as Iff
                 ( makeEvaluate, simplify )
import qualified Kore.Step.Simplification.Simplifier as Simplifier
import           Kore.Syntax.Iff
import qualified Kore.Unification.Substitution as Substitution
import qualified SMT

import           Test.Kore
import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
import qualified Test.Kore.Step.MockSimplifiers as Mock
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions
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
            assertEqualWithExplanation "" expect actual

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
        (assertEqualWithExplanation "iff(top and predicate, top and predicate)"
            (OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate =
                        makeIffPredicate
                            (makeAndPredicate
                                (makeCeilPredicate Mock.cf)
                                (makeEqualsPredicate (mkVar Mock.x) Mock.a)
                            )
                            (makeAndPredicate
                                (makeCeilPredicate Mock.cg)
                                (makeEqualsPredicate (mkVar Mock.y) Mock.b)
                            )
                    , substitution = mempty
                    }
                ]
            )
            ( makeEvaluate
                Conditional
                    { term = mkTop_
                    , predicate = makeCeilPredicate Mock.cf
                    , substitution = Substitution.wrap [(Mock.x, Mock.a)]
                    }
                Conditional
                    { term = mkTop_
                    , predicate = makeCeilPredicate Mock.cg
                    , substitution = Substitution.wrap [(Mock.y, Mock.b)]
                    }
            )
        )
    , testCase "iff with generic patterns"
        (assertEqualWithExplanation "iff(generic, generic)"
            (OrPattern.fromPatterns
                [ Conditional
                    { term =
                        mkIff
                            (mkAnd
                                (mkAnd
                                    (Mock.f Mock.a)
                                    (mkCeil_ Mock.cf)
                                )
                                (mkEquals_ (mkVar Mock.x) Mock.a)
                            )
                            (mkAnd
                                (mkAnd
                                    (Mock.g Mock.b)
                                    (mkCeil_ Mock.cg)
                                )
                                (mkEquals_ (mkVar Mock.y) Mock.b)
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
                    , substitution = Substitution.wrap [(Mock.x, Mock.a)]
                    }
                Conditional
                    { term = Mock.g Mock.b
                    , predicate = makeCeilPredicate Mock.cg
                    , substitution = Substitution.wrap [(Mock.y, Mock.b)]
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
    testCase ("iff(" ++ name a ++ ", " ++ name b ++ ")") $ do
        actual <- simplify $ makeIff [value a] [value b]
        let expect = OrPattern.fromPatterns [value r]
        assertEqualWithExplanation ("expected: " ++ name r) expect actual
  where
    name x
      | x = "⊤"
      | otherwise = "⊥"
    value x
      | x = Pattern.top
      | otherwise = Pattern.bottom
    r = a == b

testEvaluateBoolean :: HasCallStack => Bool -> Bool -> TestTree
testEvaluateBoolean a b =
    Terse.equals
        (OrPattern.fromPatterns [value r])
        (Function.on makeEvaluate value a b)
        ("iff(" ++ name a ++ ", " ++ name b ++ ")")
  where
    name x
      | x = "⊤"
      | otherwise = "⊥"
    value x
      | x = Pattern.top
      | otherwise = Pattern.bottom
    r = a == b

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
simplify iff0 =
    SMT.runSMT SMT.defaultConfig
    $ evalSimplifier emptyLogger
    $ Iff.simplify
        mockMetadataTools
        (Mock.substitutionSimplifier mockMetadataTools)
        (Simplifier.create mockMetadataTools Map.empty)
        Map.empty
        iff0

makeEvaluate
    :: Pattern Variable
    -> Pattern Variable
    -> OrPattern Variable
makeEvaluate = Iff.makeEvaluate

mockMetadataTools :: SmtMetadataTools Attribute.Symbol
mockMetadataTools =
    Mock.makeMetadataTools
        Mock.attributesMapping
        Mock.headTypeMapping
        Mock.sortAttributesMapping
        Mock.subsorts
        Mock.headSortsMapping
        Mock.smtDeclarations
