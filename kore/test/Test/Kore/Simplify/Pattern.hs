module Test.Kore.Simplify.Pattern (
    test_Pattern_simplify,
    test_Pattern_simplifyAndRemoveTopExists,
    test_Pattern_simplify_equalityterm,
) where

import Data.Maybe (fromJust)
import Data.Set qualified as Set
import Kore.Internal.Condition qualified as Condition
import Kore.Internal.From
import Kore.Internal.MultiAnd qualified as MultiAnd
import Kore.Internal.MultiOr qualified as MultiOr
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.Predicate (
    makeAndPredicate,
    makeCeilPredicate,
    makeEqualsPredicate,
    makeExistsPredicate,
    makeImpliesPredicate,
    makeNotPredicate,
 )
import Kore.Internal.Predicate qualified as Predicate
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.Pattern qualified as Pattern
import Kore.Variables.Fresh (refreshElementVariable)
import Prelude.Kore
import Test.Kore.Internal.Pattern qualified as Pattern
import Test.Kore.Rewrite.MockSymbols qualified as Mock
import Test.Kore.Simplify
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_Pattern_simplify :: [TestTree]
test_Pattern_simplify =
    [ notTop `becomes` OrPattern.bottom $
        "\\not(\\top)"
    , orAs `becomes` OrPattern.fromTermLike Mock.a $
        "\\or(a, a)"
    , bottomLike `becomes` OrPattern.bottom $
        "\\and(a, \\bottom)"
    , testCase "Removes top level exist quantifier whilst simplifying" $ do
        let expect =
                Pattern.fromTermAndPredicate
                    (Mock.constr10 fOfX)
                    ( makeAndPredicate
                        (makeCeilPredicate fOfX)
                        (makeCeilPredicate fOfY)
                    )
        actual <-
            simplify
                ( Pattern.fromTermAndPredicate
                    (Mock.constr10 fOfX)
                    ( makeAndPredicate
                        (makeCeilPredicate fOfX)
                        ( makeExistsPredicate
                            Mock.yConfig
                            ( makeAndPredicate
                                (makeCeilPredicate fOfX)
                                (makeCeilPredicate fOfY)
                            )
                        )
                    )
                )
        assertEqual "" (OrPattern.fromPattern expect) actual
    , testCase "Simplifies multiple Implies" $ do
        let expect =
                Pattern.fromTermAndPredicate
                    (Mock.constr10 fOfX)
                    ( Predicate.fromMultiAnd . MultiAnd.make $
                        [ makeCeilPredicate fOfX
                        , makeCeilPredicate fOfY
                        , makeCeilPredicate gOfX
                        , makeEqualsPredicate fOfX gOfX
                        ]
                    )
                    & OrPattern.fromPattern
        actual <-
            simplify $
                Pattern.fromTermAndPredicate
                    ( mkAnd
                        (Mock.constr10 fOfX)
                        (Mock.constr10 gOfX)
                    )
                    ( Predicate.fromMultiAnd . MultiAnd.make $
                        [ makeCeilPredicate fOfX
                        , makeImpliesPredicate
                            (makeCeilPredicate fOfX)
                            (makeCeilPredicate gOfX)
                        , makeImpliesPredicate
                            (makeCeilPredicate gOfX)
                            (makeCeilPredicate fOfY)
                        ]
                    )
        Pattern.assertEquivalentPatterns expect actual
    , testCase "Does not replace and terms under intersecting quantifiers" $ do
        let x = Mock.xConfig
            x' =
                refreshElementVariable
                    (Set.singleton $ inject $ variableName x)
                    x
                    & fromJust
            expect =
                Pattern.fromTermAndPredicate
                    (Mock.constr10 fOfX)
                    ( makeAndPredicate
                        (makeCeilPredicate fOfX)
                        (fromCeil_ $ Mock.f (mkElemVar x'))
                    )
                    & OrPattern.fromPattern
        actual <-
            simplify $
                Pattern.fromTermAndPredicate
                    (Mock.constr10 fOfX)
                    ( makeAndPredicate
                        (makeCeilPredicate fOfX)
                        ( makeExistsPredicate
                            Mock.xConfig
                            (makeCeilPredicate fOfX)
                        )
                    )
        Pattern.assertEquivalentPatterns expect actual
    , testCase "Contradictions result in bottom" $ do
        actual <-
            simplify $
                Pattern.fromTermAndPredicate
                    (Mock.constr10 fOfX)
                    ( makeAndPredicate
                        (makeCeilPredicate fOfX)
                        (makeNotPredicate $ makeCeilPredicate fOfX)
                    )
        assertEqual "" mempty actual
    , testCase "Simplifies Implies - Positive" $ do
        let expect =
                Pattern.fromTermAndPredicate
                    (Mock.constr10 fOfX)
                    ( Predicate.fromMultiAnd . MultiAnd.make $
                        [ makeCeilPredicate fOfX
                        , makeCeilPredicate gOfX
                        , makeEqualsPredicate fOfX gOfX
                        ]
                    )
                    & OrPattern.fromPattern
        actual <-
            simplify $
                Pattern.fromTermAndPredicate
                    ( mkAnd
                        (Mock.constr10 fOfX)
                        (Mock.constr10 gOfX)
                    )
                    ( makeAndPredicate
                        (makeCeilPredicate fOfX)
                        ( makeImpliesPredicate
                            (makeCeilPredicate fOfX)
                            (makeCeilPredicate gOfX)
                        )
                    )
        Pattern.assertEquivalentPatterns expect actual
    , testCase "Simplifies Implies - Negative" $ do
        let expect =
                Pattern.fromTermAndPredicate
                    (Mock.constr10 fOfX)
                    ( (Predicate.fromMultiAnd . MultiAnd.make)
                        [ makeEqualsPredicate fOfX gOfX
                        , makeNotPredicate $ makeCeilPredicate fOfX
                        ]
                    )
        actual <-
            simplify $
                Pattern.fromTermAndPredicate
                    ( mkAnd
                        (Mock.constr10 fOfX)
                        (Mock.constr10 gOfX)
                    )
                    ( makeAndPredicate
                        (makeNotPredicate $ makeCeilPredicate fOfX)
                        ( makeImpliesPredicate
                            (makeCeilPredicate fOfX)
                            (makeCeilPredicate gOfX)
                        )
                    )
        assertEqual "" (OrPattern.fromPattern expect) actual
    ]
  where
    fOfX = Mock.f (mkElemVar Mock.xConfig)
    fOfY = Mock.f (mkElemVar Mock.yConfig)
    gOfX = Mock.g (mkElemVar Mock.xConfig)
    becomes ::
        HasCallStack =>
        Pattern RewritingVariableName ->
        OrPattern RewritingVariableName ->
        String ->
        TestTree
    becomes original expect name =
        testCase name $ do
            actual <- simplify original
            assertEqual "" expect actual

test_Pattern_simplify_equalityterm :: [TestTree]
test_Pattern_simplify_equalityterm =
    [ testCase "f vs g or h" $ do
        let expected =
                (OrPattern.fromOrCondition Mock.testSort . MultiOr.make)
                    [ Condition.fromPredicate
                        ( Predicate.fromMultiAnd . MultiAnd.make $
                            [ makeCeilPredicate Mock.cf
                            , makeCeilPredicate Mock.cg
                            , makeEqualsPredicate Mock.cf Mock.cg
                            , makeNotPredicate (makeCeilPredicate Mock.ch)
                            ]
                        )
                    , Condition.fromPredicate
                        ( Predicate.fromMultiAnd . MultiAnd.make $
                            [ makeCeilPredicate Mock.cf
                            , makeCeilPredicate Mock.cg
                            , makeCeilPredicate Mock.ch
                            , makeEqualsPredicate Mock.cf Mock.cg
                            , makeEqualsPredicate Mock.cf Mock.ch
                            ]
                        )
                    , Condition.fromPredicate
                        ( Predicate.fromMultiAnd . MultiAnd.make $
                            [ makeCeilPredicate Mock.cf
                            , makeCeilPredicate Mock.ch
                            , makeEqualsPredicate Mock.cf Mock.ch
                            , makeNotPredicate $ makeCeilPredicate Mock.cg
                            ]
                        )
                    , Condition.fromPredicate
                        ( Predicate.fromMultiAnd . MultiAnd.make $
                            [ makeCeilPredicate Mock.cf
                            , makeCeilPredicate Mock.ch
                            , makeCeilPredicate Mock.cg
                            , makeEqualsPredicate Mock.cf Mock.ch
                            , makeEqualsPredicate Mock.cf Mock.cg
                            ]
                        )
                    , Condition.fromPredicate
                        ( Predicate.fromMultiAnd . MultiAnd.make $
                            [ makeNotPredicate $ makeCeilPredicate Mock.cf
                            , makeNotPredicate $ makeCeilPredicate Mock.cg
                            , makeNotPredicate $ makeCeilPredicate Mock.ch
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
                        ( Predicate.fromMultiAnd . MultiAnd.make $
                            [ makeCeilPredicate Mock.cf
                            , makeCeilPredicate Mock.ch
                            , makeEqualsPredicate Mock.cf Mock.ch
                            , makeNotPredicate $ makeCeilPredicate Mock.cg
                            ]
                        )
                    , Pattern.fromTermAndPredicate
                        (mkTop Mock.testSort)
                        ( Predicate.fromMultiAnd . MultiAnd.make $
                            [ makeNotPredicate $ makeCeilPredicate Mock.cf
                            , makeNotPredicate $ makeCeilPredicate Mock.cg
                            , makeNotPredicate $ makeCeilPredicate Mock.ch
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
        let definedF = makeCeilPredicate Mock.cf
            definedG = makeCeilPredicate Mock.cg
            predicateSubstitution =
                makeEqualsPredicate (mkElemVar Mock.xConfig) Mock.a
            definedGWithSubstitution =
                (Predicate.fromMultiAnd . MultiAnd.make)
                    [definedG, predicateSubstitution]
            definedH = makeCeilPredicate Mock.ch
            expected =
                (OrPattern.fromOrCondition Mock.testSort . MultiOr.make)
                    [ mconcat
                        [ (Condition.fromPredicate . Predicate.fromMultiAnd . MultiAnd.make)
                            [ definedF
                            , definedG
                            , makeEqualsPredicate Mock.cf Mock.cg
                            , makeNotPredicate definedH
                            ]
                        , Condition.assign (inject Mock.xConfig) Mock.a
                        ]
                    , mconcat
                        [ (Condition.fromPredicate . Predicate.fromMultiAnd . MultiAnd.make)
                            [ definedF
                            , definedG
                            , definedH
                            , makeEqualsPredicate Mock.cf Mock.cg
                            , makeEqualsPredicate Mock.cf Mock.ch
                            ]
                        , Condition.assign (inject Mock.xConfig) Mock.a
                        ]
                    , Condition.fromPredicate
                        ( Predicate.fromMultiAnd . MultiAnd.make $
                            [ definedF
                            , definedH
                            , makeEqualsPredicate Mock.cf Mock.ch
                            , makeNotPredicate definedGWithSubstitution
                            ]
                        )
                    , Condition.fromPredicate
                        ( Predicate.fromMultiAnd . MultiAnd.make $
                            [ makeNotPredicate definedGWithSubstitution
                            , makeNotPredicate definedF
                            , makeNotPredicate definedH
                            ]
                        )
                    ]
            first = Mock.cf
            second =
                (OrPattern.toTermLike Mock.testSort . OrPattern.fromPatterns)
                    [ (Pattern.withCondition Mock.cg)
                        (Condition.assign (inject Mock.xConfig) Mock.a)
                    , Pattern.fromTermLike Mock.ch
                    ]
        assertBidirectionalEqualityResult first second expected
    ]

test_Pattern_simplifyAndRemoveTopExists :: [TestTree]
test_Pattern_simplifyAndRemoveTopExists =
    [ notTop `becomes` OrPattern.bottom $
        "\\not(\\top)"
    , orAs `becomes` OrPattern.fromTermLike Mock.a $
        "\\or(a, a)"
    , bottomLike `becomes` OrPattern.bottom $
        "\\and(a, \\bottom)"
    , existential `becomes` OrPattern.fromTermLike unquantified $
        "..."
    , multiexistential `becomes` OrPattern.fromTermLike unquantified $
        "..."
    , universal `becomes` OrPattern.fromPattern universal $
        "..."
    , existentialuniversal `becomes` OrPattern.fromPattern universal $
        "..."
    ]
  where
    becomes ::
        HasCallStack =>
        Pattern RewritingVariableName ->
        OrPattern RewritingVariableName ->
        String ->
        TestTree
    becomes original expect name =
        testCase name $ do
            actual <- simplifyAndRemoveTopExists original
            assertEqual "" expect actual
    unquantified = Mock.sigma (mkElemVar Mock.xConfig) (mkElemVar Mock.yConfig)
    existential = termLike (mkExists Mock.xConfig unquantified)
    multiexistential =
        termLike (mkExists Mock.yConfig (mkExists Mock.xConfig unquantified))
    universal = termLike (mkForall Mock.xConfig unquantified)
    existentialuniversal =
        termLike (mkExists Mock.yConfig (mkForall Mock.xConfig unquantified))

termLike :: TermLike RewritingVariableName -> Pattern RewritingVariableName
termLike = Pattern.fromTermLike

-- | Term is \bottom, but not in a trivial way.
notTop, orAs, bottomLike :: Pattern RewritingVariableName
notTop = termLike (mkNot $ mkTop Mock.testSort)

-- | Lifting disjunction to the top would duplicate terms.
orAs = termLike (mkOr Mock.a Mock.a)

-- | Term is defined, but predicate is \bottom.
bottomLike =
    (termLike Mock.a){Pattern.predicate = Predicate.makeFalsePredicate}

simplify ::
    Pattern RewritingVariableName ->
    IO (OrPattern RewritingVariableName)
simplify = testRunSimplifier Mock.env . Pattern.simplify

simplifyAndRemoveTopExists ::
    Pattern RewritingVariableName ->
    IO (OrPattern RewritingVariableName)
simplifyAndRemoveTopExists =
    testRunSimplifier Mock.env
        . Pattern.simplifyTopConfiguration

assertBidirectionalEqualityResult ::
    HasCallStack =>
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    OrPattern RewritingVariableName ->
    IO ()
assertBidirectionalEqualityResult child1 child2 expected = do
    testOneDirection (mkEquals Mock.testSort child1 child2)
    testOneDirection (mkEquals Mock.testSort child2 child1)
  where
    testOneDirection term = do
        actual <- simplify (Pattern.fromTermLike term)
        Pattern.assertEquivalentPatterns expected actual
