module Test.Kore.Step.Simplification.Pattern
    ( test_Pattern_simplify
    , test_Pattern_simplifyAndRemoveTopExists
    , test_Pattern_simplify_equalityterm
    ) where

import Prelude.Kore

import Test.Tasty

import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Conditional (..)
    , Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( makeAndPredicate
    , makeCeilPredicate
    , makeCeilPredicate_
    , makeEqualsPredicate
    , makeEqualsPredicate_
    , makeExistsPredicate
    , makeImpliesPredicate
    , makeNotPredicate
    )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
import qualified Kore.Step.Simplification.Pattern as Pattern
import Kore.TopBottom
    ( isBottom
    )

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext

test_Pattern_simplify :: [TestTree]
test_Pattern_simplify =
    [ notTop     `becomes` OrPattern.bottom
        $ "\\not(\\top)"
    , orAs       `becomes` OrPattern.fromTermLike Mock.a
        $ "\\or(a, a)"
    , bottomLike `becomes` OrPattern.bottom
        $ "\\and(a, \\bottom)"
    , testGroup "Local function evaluation" $
        let f = Mock.f (mkElemVar Mock.x)
            fInt = Mock.fInt (mkElemVar Mock.xInt)
            defined = makeCeilPredicate_ f & Condition.fromPredicate
            a = Mock.a
            b = Mock.b
            injA = Mock.sortInjection10 Mock.a
            injB = Mock.sortInjection10 Mock.b
            int2 = Mock.builtinInt 2
            int3 = Mock.builtinInt 3
            mkLocalDefn func (Left t)  = makeEqualsPredicate_ t func
            mkLocalDefn func (Right t) = makeEqualsPredicate_ func t
            test name func eitherC1 eitherC2 =
                testCase name $ do
                    let equals1 = mkLocalDefn func eitherC1 & Condition.fromPredicate
                        equals2 = mkLocalDefn func eitherC2 & Condition.fromPredicate
                        patt =
                            Pattern.fromCondition_
                                ( defined <> equals1
                                <> defined <> equals2
                                )
                    actual <- simplify patt
                    assertBool "Expected \\bottom" $ isBottom actual
        in
            [ -- Constructor at top
              test "contradiction: f(x) = a ∧ f(x) = b" f (Right a) (Right b)
            , test "contradiction: a = f(x) ∧ f(x) = b" f (Left  a) (Right b)
            , test "contradiction: a = f(x) ∧ b = f(x)" f (Left  a) (Left  b)
            , test "contradiction: f(x) = a ∧ b = f(x)" f (Right a) (Left  b)
            -- Sort injection at top
            , test "contradiction: f(x) = injA ∧ f(x) = injB" f (Right injA) (Right injB)
            , test "contradiction: injA = f(x) ∧ f(x) = injB" f (Left  injA) (Right injB)
            , test "contradiction: injA = f(x) ∧ injB = f(x)" f (Left  injA) (Left  injB)
            , test "contradiction: f(x) = injA ∧ injB = f(x)" f (Right injA) (Left  injB)
            -- Builtin at top
            , test "contradiction: f(x) = 2 ∧ f(x) = 3" fInt (Right int2) (Right int3)
            , test "contradiction: 2 = f(x) ∧ f(x) = 3" fInt (Left  int2) (Right int3)
            , test "contradiction: 2 = f(x) ∧ 3 = f(x)" fInt (Left  int2) (Left  int3)
            , test "contradiction: f(x) = 2 ∧ 3 = f(x)" fInt (Right int2) (Left  int3)
            ]
    , testCase "Replaces and terms under independent quantifiers" $ do
        let expect =
                Pattern.fromTermAndPredicate
                    (Mock.constr10 fOfX)
                    (makeAndPredicate
                        (makeCeilPredicate Mock.testSort fOfX)
                        (makeExistsPredicate Mock.y
                            (makeCeilPredicate Mock.testSort fOfY)
                        )
                    )
        actual <-
            simplify
                (Pattern.fromTermAndPredicate
                    (Mock.constr10 fOfX)
                    (makeAndPredicate
                        (makeCeilPredicate Mock.testSort fOfX)
                        (makeExistsPredicate Mock.y
                            (makeAndPredicate
                                (makeCeilPredicate Mock.testSort fOfX)
                                (makeCeilPredicate Mock.testSort fOfY)
                            )
                        )
                    )
                )
        assertEqual "" (OrPattern.fromPattern expect) actual
    , testCase "Simplifies multiple Implies" $ do
        let expect =
                Pattern.fromTermAndPredicate
                    (Mock.constr10 fOfX)
                    ( MultiAnd.toPredicate . MultiAnd.make $
                    [ makeCeilPredicate Mock.testSort fOfX
                    , makeCeilPredicate Mock.testSort fOfY
                    , makeCeilPredicate Mock.testSort gOfX
                    , makeEqualsPredicate_ fOfX gOfX
                    ]
                    )
        actual <-
            simplify
                $ Pattern.fromTermAndPredicate
                    (mkAnd
                        (Mock.constr10 fOfX)
                        (Mock.constr10 gOfX)
                    )
                    ( MultiAnd.toPredicate . MultiAnd.make $
                    [ makeCeilPredicate_ fOfX
                    , makeImpliesPredicate
                        (makeCeilPredicate_ fOfX)
                        (makeCeilPredicate_ gOfX)
                    , makeImpliesPredicate
                        (makeCeilPredicate_ gOfX)
                        (makeCeilPredicate_ fOfY)
                    ]
                    )
        assertEqual "" (OrPattern.fromPattern expect) actual
    , testCase "Does not replace and terms under intersecting quantifiers" $ do
        let expect =
                Pattern.fromTermAndPredicate
                    (Mock.constr10 fOfX)
                     (makeAndPredicate
                         (makeCeilPredicate Mock.testSort fOfX)
                         (makeExistsPredicate Mock.x
                             (makeCeilPredicate Mock.testSort fOfX)
                         )
                     )
        actual <-
            simplify $
                Pattern.fromTermAndPredicate
                    (Mock.constr10 fOfX)
                    (makeAndPredicate
                        (makeCeilPredicate_ fOfX)
                        (makeExistsPredicate Mock.x (makeCeilPredicate_ fOfX))
                    )
        assertEqual "" (OrPattern.fromPattern expect) actual
    , testCase "Contradictions result in bottom" $ do
        actual <-
            simplify $
                Pattern.fromTermAndPredicate
                    (Mock.constr10 fOfX)
                    (makeAndPredicate
                        (makeCeilPredicate_ fOfX)
                        (mkNot <$> makeCeilPredicate_ fOfX)
                    )
        assertEqual "" mempty actual
    , testCase "Simplifies Implies - Positive" $ do
        let expect =
                Pattern.fromTermAndPredicate
                    (Mock.constr10 fOfX)
                    (MultiAnd.toPredicate . MultiAnd.make $
                    [ makeCeilPredicate Mock.testSort fOfX
                    , makeCeilPredicate Mock.testSort gOfX
                    , makeEqualsPredicate_ fOfX gOfX
                    ]
                    )
        actual <-
            simplify $
                Pattern.fromTermAndPredicate
                    (mkAnd
                        (Mock.constr10 fOfX)
                        (Mock.constr10 gOfX)
                    )
                    (makeAndPredicate
                        (makeCeilPredicate_ fOfX)
                        (makeImpliesPredicate
                            (makeCeilPredicate_ fOfX)
                            (makeCeilPredicate_ gOfX)
                        )
                    )
        assertEqual "" (OrPattern.fromPattern expect) actual
    , testCase "Simplifies Implies - Negative" $ do
        let expect =
                Pattern.fromTermAndPredicate
                    (Mock.constr10 fOfX)
                    (makeAndPredicate
                        (makeEqualsPredicate Mock.testSort fOfX gOfX)
                        (makeNotPredicate $ makeCeilPredicate Mock.testSort fOfX)
                    )
        actual <-
            simplify $
                Pattern.fromTermAndPredicate
                    (mkAnd
                        (Mock.constr10 fOfX)
                        (Mock.constr10 gOfX)
                    )
                    (makeAndPredicate
                        (makeNotPredicate $ makeCeilPredicate_ fOfX)
                        (makeImpliesPredicate
                            (makeCeilPredicate_ fOfX)
                            (makeCeilPredicate_ gOfX)
                        )
                    )
        assertEqual "" (OrPattern.fromPattern expect) actual
    ]
  where
    fOfX = Mock.f (mkElemVar Mock.x)
    fOfY = Mock.f (mkElemVar Mock.y)
    gOfX = Mock.g (mkElemVar Mock.x)
    becomes
        :: HasCallStack
        => Pattern VariableName -> OrPattern VariableName -> String -> TestTree
    becomes original expect name =
        testCase name $ do
            actual <- simplify original
            assertEqual "" expect actual

test_Pattern_simplify_equalityterm :: [TestTree]
test_Pattern_simplify_equalityterm =
    [ testCase "f vs g or h" $ do
        let expected =
                OrPattern.fromPatterns
                    [ Pattern.fromTermAndPredicate
                        (mkTop Mock.testSort)
                        (MultiAnd.toPredicate . MultiAnd.make $
                        [ makeCeilPredicate Mock.testSort Mock.cf
                        , makeCeilPredicate Mock.testSort Mock.cg
                        , makeEqualsPredicate Mock.testSort Mock.cf Mock.cg
                        , makeImpliesPredicate
                            (makeCeilPredicate Mock.testSort Mock.ch)
                            (makeEqualsPredicate Mock.testSort Mock.cf Mock.ch)
                        ]
                        )
                    , Pattern.fromTermAndPredicate
                        (mkTop Mock.testSort)
                        (MultiAnd.toPredicate . MultiAnd.make $
                        [ makeCeilPredicate Mock.testSort Mock.cf
                        , makeCeilPredicate Mock.testSort Mock.ch
                        , makeEqualsPredicate Mock.testSort Mock.cf Mock.ch
                        , makeImpliesPredicate
                            (makeCeilPredicate Mock.testSort Mock.cg)
                            (makeEqualsPredicate Mock.testSort Mock.cf Mock.cg)
                        ]
                        )
                    , Pattern.fromTermAndPredicate
                        (mkTop Mock.testSort)
                        (MultiAnd.toPredicate . MultiAnd.make $
                        [ makeNotPredicate $ makeCeilPredicate Mock.testSort Mock.cf
                        , makeNotPredicate $ makeCeilPredicate Mock.testSort Mock.cg
                        , makeNotPredicate $ makeCeilPredicate Mock.testSort Mock.ch
                        ]
                        )
                    ]
            first = Mock.cf
            second = mkOr Mock.cg Mock.ch
        assertBidirectionalEqualityResult first second expected
    , testCase "f vs g or h where f /= g" $ do
        let expected =
                OrPattern.fromPatterns
                    [ Pattern.fromTermAndPredicate
                        (mkTop Mock.testSort)
                        (MultiAnd.toPredicate . MultiAnd.make $
                        [ makeCeilPredicate Mock.testSort Mock.cf
                        , makeCeilPredicate Mock.testSort Mock.ch
                        , makeEqualsPredicate Mock.testSort Mock.cf Mock.ch
                        , makeNotPredicate $ makeCeilPredicate Mock.testSort Mock.cg
                        ]
                        )
                    , Pattern.fromTermAndPredicate
                        (mkTop Mock.testSort)
                        (MultiAnd.toPredicate . MultiAnd.make $
                        [ makeNotPredicate $ makeCeilPredicate Mock.testSort Mock.cf
                        , makeNotPredicate $ makeCeilPredicate Mock.testSort Mock.cg
                        , makeNotPredicate $ makeCeilPredicate Mock.testSort Mock.ch
                        ]
                        )
                    ]
            first = Mock.functionalConstr10 Mock.cf
            second =
                mkOr
                    (Mock.functionalConstr11 Mock.cg)
                    (Mock.functionalConstr10 Mock.ch)
        assertBidirectionalEqualityResult first second expected
    , testCase "f vs g[x = a] or h" $ do
        let definedF = makeCeilPredicate Mock.testSort Mock.cf
            definedG = makeCeilPredicate Mock.testSort Mock.cg
            predicateSubstitution =
                makeEqualsPredicate Mock.testSort (mkElemVar Mock.x) Mock.a
            definedGWithSubstitution =
                makeAndPredicate
                    definedG
                    predicateSubstitution
            definedH = makeCeilPredicate Mock.testSort Mock.ch
            expected =
                OrPattern.fromPatterns
                    [ Conditional
                        { term = mkTop Mock.testSort
                        , predicate =
                            (MultiAnd.toPredicate . MultiAnd.make)
                            [ definedF
                            , definedG
                            , makeEqualsPredicate Mock.testSort Mock.cf Mock.cg
                            , makeImpliesPredicate
                                definedH
                                (makeEqualsPredicate Mock.testSort Mock.cf Mock.ch)
                            ]
                        , substitution = Substitution.unsafeWrap
                            [(inject Mock.x, Mock.a)]
                        }
                    , Pattern.fromTermAndPredicate
                        (mkTop Mock.testSort)
                        (MultiAnd.toPredicate . MultiAnd.make $
                        [ definedF
                        , definedH
                        , makeEqualsPredicate Mock.testSort Mock.cf Mock.ch
                        , makeImpliesPredicate
                            definedGWithSubstitution
                            (makeEqualsPredicate Mock.testSort Mock.cf Mock.cg)
                        ]
                        )
                    , Pattern.fromTermAndPredicate
                        (mkTop Mock.testSort)
                        (MultiAnd.toPredicate . MultiAnd.make $
                        [ makeNotPredicate definedGWithSubstitution
                        , makeNotPredicate definedF
                        , makeNotPredicate definedH
                        ]
                        )
                    ]
            first = Mock.cf
            second =
                OrPattern.toTermLike
                . OrPattern.fromPatterns $
                    [ Conditional
                        { term = Mock.cg
                        , predicate = Predicate.makeTruePredicate Mock.testSort
                        , substitution =
                            Substitution.wrap
                            $ Substitution.mkUnwrappedSubstitution
                            [(inject Mock.x, Mock.a)]
                        }
                    , Conditional
                        { term = Mock.ch
                        , predicate = Predicate.makeTruePredicate Mock.testSort
                        , substitution = mempty
                        }
                    ]
        assertBidirectionalEqualityResult first second expected
    ]

test_Pattern_simplifyAndRemoveTopExists :: [TestTree]
test_Pattern_simplifyAndRemoveTopExists =
    [ notTop      `becomes` OrPattern.bottom
        $ "\\not(\\top)"
    , orAs        `becomes` OrPattern.fromTermLike Mock.a
        $ "\\or(a, a)"
    , bottomLike  `becomes` OrPattern.bottom
        $ "\\and(a, \\bottom)"
    , existential `becomes` OrPattern.fromTermLike unquantified
        $ "..."
    , multiexistential `becomes` OrPattern.fromTermLike unquantified
        $ "..."
    , universal `becomes` OrPattern.fromPattern universal
        $ "..."
    , existentialuniversal `becomes` OrPattern.fromPattern universal
        $ "..."
    ]
  where
    becomes
        :: HasCallStack
        => Pattern VariableName -> OrPattern VariableName -> String -> TestTree
    becomes original expect name =
        testCase name $ do
            actual <- simplifyAndRemoveTopExists original
            assertEqual "" expect actual
    unquantified = Mock.sigma (mkElemVar Mock.x) (mkElemVar Mock.y)
    existential = termLike (mkExists Mock.x unquantified)
    multiexistential = termLike (mkExists Mock.y (mkExists Mock.x unquantified))
    universal = termLike (mkForall Mock.x unquantified)
    existentialuniversal =
        termLike (mkExists Mock.y (mkForall Mock.x unquantified))

termLike :: TermLike VariableName -> Pattern VariableName
termLike = Pattern.fromTermLike

-- | Term is \bottom, but not in a trivial way.
notTop, orAs, bottomLike :: Pattern VariableName
notTop = termLike (mkNot mkTop_)
-- | Lifting disjunction to the top would duplicate terms.
orAs = termLike (mkOr Mock.a Mock.a)
-- | Term is defined, but predicate is \bottom.
bottomLike =
    (termLike Mock.a) { Pattern.predicate = Predicate.makeFalsePredicate_ }

simplify :: Pattern VariableName -> IO (OrPattern VariableName)
simplify = runSimplifier Mock.env . Pattern.simplify

simplifyAndRemoveTopExists :: Pattern VariableName -> IO (OrPattern VariableName)
simplifyAndRemoveTopExists =
    runSimplifier Mock.env
    . Pattern.simplifyTopConfiguration

assertBidirectionalEqualityResult
    :: TermLike VariableName
    -> TermLike VariableName
    -> OrPattern VariableName
    -> IO ()
assertBidirectionalEqualityResult child1 child2 expected = do
    testOneDirection (mkEquals Mock.testSort child1 child2)
    testOneDirection (mkEquals Mock.testSort child2 child1)
  where
    testOneDirection term = do
        actual <- simplify (Pattern.fromTermLike term)
        assertEqual "" expected actual
