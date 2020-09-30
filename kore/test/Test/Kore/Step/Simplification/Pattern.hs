module Test.Kore.Step.Simplification.Pattern
    ( test_Pattern_simplify
    , test_Pattern_simplifyAndRemoveTopExists
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
    ( Pattern
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
import qualified Kore.Internal.SideCondition as SideCondition
    ( top
    )
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
            defined = makeCeilPredicate_ f & Condition.fromPredicate
            a = Mock.a
            b = Mock.b
            mkLocalDefn (Left t)  = makeEqualsPredicate_ t f
            mkLocalDefn (Right t) = makeEqualsPredicate_ f t
            test name eitherC1 eitherC2 =
                testCase name $ do
                    let equals1 = mkLocalDefn eitherC1 & Condition.fromPredicate
                        equals2 = mkLocalDefn eitherC2 & Condition.fromPredicate
                        patt =
                            Pattern.fromCondition_
                                ( defined <> equals1
                                <> defined <> equals2
                                )
                    actual <- simplify patt
                    assertBool "Expected \\bottom" $ isBottom actual
        in
            [ test "contradiction: f(x) = a ∧ f(x) = b" (Right a) (Right b)
            , test "contradiction: a = f(x) ∧ f(x) = b" (Left  a) (Right b)
            , test "contradiction: a = f(x) ∧ b = f(x)" (Left  a) (Left  b)
            , test "contradiction: f(x) = a ∧ b = f(x)" (Right a) (Left  b)
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
simplify = runSimplifier Mock.env . Pattern.simplify SideCondition.top

simplifyAndRemoveTopExists :: Pattern VariableName -> IO (OrPattern VariableName)
simplifyAndRemoveTopExists =
    runSimplifier Mock.env
    . Pattern.simplifyTopConfiguration
