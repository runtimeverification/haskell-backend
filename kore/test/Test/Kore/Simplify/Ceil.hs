module Test.Kore.Simplify.Ceil (
    test_ceilSimplification,
) where

import Data.Map.Strict qualified as Map
import Kore.Equation (Equation)
import Kore.Internal.Condition as Condition
import Kore.Internal.From (fromTop_)
import Kore.Internal.MultiAnd qualified as MultiAnd
import Kore.Internal.MultiOr qualified as MultiOr
import Kore.Internal.NormalForm (NormalForm)
import Kore.Internal.NormalForm qualified as NormalForm (
    fromPredicate,
    fromPredicates,
 )
import Kore.Internal.Predicate (
    makeCeilPredicate,
    makeEqualsPredicate,
    makeTruePredicate,
 )
import Kore.Internal.SideCondition qualified as SideCondition (
    top,
 )
import Kore.Internal.Substitution qualified as Substitution
import Kore.Internal.TermLike as TermLike
import Kore.Rewrite.Axiom.Identifier qualified as AxiomIdentifier (
    AxiomIdentifier (..),
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.Ceil qualified as Ceil
import Kore.Simplify.Simplify
import Prelude.Kore
import Test.Kore.Internal.OrPattern (
    OrPattern,
 )
import Test.Kore.Internal.OrPattern qualified as OrPattern
import Test.Kore.Internal.Pattern as Pattern
import Test.Kore.Rewrite.MockSymbols (
    testSort,
 )
import Test.Kore.Rewrite.MockSymbols qualified as Mock
import Test.Kore.Simplify
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_ceilSimplification :: [TestTree]
test_ceilSimplification =
    [ testCase "Ceil - or distribution" $ do
        -- ceil(a or b) = (top and ceil(a)) or (top and ceil(b))
        let expected =
                MultiOr.make
                    [ MultiAnd.make
                        [ makeCeilPredicate somethingOfA
                        , makeCeilPredicate Mock.a
                        ]
                    , MultiAnd.make
                        [ makeCeilPredicate somethingOfB
                        , makeCeilPredicate Mock.b
                        ]
                    ]
        actual <-
            evaluate
                ( makeCeil
                    [somethingOfAExpanded, somethingOfBExpanded]
                )
        assertEqual "" expected actual
    , testCase
        "Ceil - bool operations"
        ( do
            -- ceil(top) = top
            actual1 <-
                evaluate
                    ( makeCeil
                        [Pattern.topOf Mock.testSort]
                    )
            assertEqual
                "ceil(top)"
                (NormalForm.fromPredicate fromTop_)
                actual1
            -- ceil(bottom) = bottom
            actual2 <-
                evaluate
                    ( makeCeil
                        []
                    )
            assertEqual
                "ceil(bottom)"
                MultiOr.bottom
                actual2
        )
    , testCase
        "Ceil - sorted bool operations"
        ( do
            -- ceil(top{testSort}) = top
            actual1 <-
                evaluate
                    ( makeCeil
                        [Pattern.fromCondition Mock.testSort Condition.top]
                    )
            assertEqual
                "ceil(top)"
                (NormalForm.fromPredicate fromTop_)
                actual1
        )
    , testCase
        "expanded Ceil - bool operations"
        ( do
            -- ceil(top) = top
            actual1 <- makeEvaluate (Pattern.topOf Mock.testSort)
            assertEqual
                "ceil(top)"
                (NormalForm.fromPredicate fromTop_)
                actual1
            -- ceil(bottom) = bottom
            actual2 <- makeEvaluate (Pattern.bottomOf Mock.testSort)
            assertEqual
                "ceil(bottom)"
                MultiOr.bottom
                actual2
        )
    , testCase "ceil with predicates and substitutions" $ do
        -- if term is not functional, then
        -- ceil(term and predicate and subst)
        --     = top and (ceil(term) and predicate) and subst
        let expected =
                NormalForm.fromPredicates
                    [ makeCeilPredicate somethingOfA
                    , makeCeilPredicate Mock.a
                    , makeEqualsPredicate fOfA gOfA
                    , makeEqualsPredicate (mkElemVar Mock.xConfig) fOfB
                    ]
        actual <-
            makeEvaluate
                Conditional
                    { term = somethingOfA
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution =
                        Substitution.wrap
                            $ Substitution.mkUnwrappedSubstitution
                                [(inject Mock.xConfig, fOfB)]
                    }
        assertEqual
            "ceil(something(a) and equals(f(a), g(a)))"
            expected
            actual
    , let constructorTerm = Mock.constr20 somethingOfA somethingOfB
       in testCase "ceil with constructors" $ do
            -- if term is a non-functional-constructor(params), then
            -- ceil(term and predicate and subst)
            --     = top and (ceil(term) and predicate) and subst
            let expected =
                    NormalForm.fromPredicates
                        [ makeCeilPredicate somethingOfA
                        , makeCeilPredicate somethingOfB
                        , makeEqualsPredicate fOfA gOfA
                        , makeEqualsPredicate (mkElemVar Mock.xConfig) fOfB
                        ]
            actual <-
                makeEvaluate
                    Conditional
                        { term = constructorTerm
                        , predicate = makeEqualsPredicate fOfA gOfA
                        , substitution =
                            Substitution.wrap
                                $ Substitution.mkUnwrappedSubstitution
                                    [(inject Mock.xConfig, fOfB)]
                        }
            assertEqual
                "ceil(constr(something(a), something(b)) and eq(f(a), g(a)))"
                expected
                actual
    , testCase "ceil of constructors is top" $ do
        let expected = NormalForm.fromPredicate fromTop_
        actual <-
            makeEvaluate
                Conditional
                    { term = Mock.constr10 Mock.a
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        assertEqual "" expected actual
    , testCase "ceil with functional symbols" $ do
        -- if term is a functional(params), then
        -- ceil(term and predicate and subst)
        --     = top and (ceil(params) and predicate) and subst
        let expected =
                NormalForm.fromPredicates
                    [ makeCeilPredicate somethingOfA
                    , makeCeilPredicate somethingOfB
                    , makeEqualsPredicate fOfA gOfA
                    , makeEqualsPredicate (mkElemVar Mock.xConfig) fOfB
                    ]
        actual <-
            makeEvaluate
                Conditional
                    { term = Mock.functional20 somethingOfA somethingOfB
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution =
                        Substitution.wrap
                            $ Substitution.mkUnwrappedSubstitution
                                [(inject Mock.xConfig, fOfB)]
                    }
        assertEqual
            "ceil(functional(something(a), something(b)) and eq(f(a), g(a)))"
            expected
            actual
    , testCase "ceil with function symbols" $ do
        -- if term is a function(params), then
        -- ceil(term and predicate and subst)
        --     = top and (ceil(term) and predicate) and subst
        let expected =
                NormalForm.fromPredicates
                    [ makeCeilPredicate fOfA
                    , makeCeilPredicate Mock.a
                    , makeEqualsPredicate fOfA gOfA
                    , makeEqualsPredicate (mkElemVar Mock.xConfig) fOfB
                    ]
        actual <-
            makeEvaluate
                Conditional
                    { term = fOfA
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution =
                        Substitution.wrap
                            $ Substitution.mkUnwrappedSubstitution
                                [(inject Mock.xConfig, fOfB)]
                    }
        assertEqual
            "ceil(f(a)) and eq(f(a), g(a)))"
            expected
            actual
    , testCase "ceil with functional terms" $ do
        -- if term is functional, then
        -- ceil(term and predicate and subst)
        --     = top and predicate and subst
        let expected =
                NormalForm.fromPredicates
                    [ makeEqualsPredicate fOfA gOfA
                    , makeEqualsPredicate (mkElemVar Mock.xConfig) fOfB
                    ]
        actual <-
            makeEvaluate
                Conditional
                    { term = Mock.a
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution =
                        Substitution.wrap
                            $ Substitution.mkUnwrappedSubstitution
                                [(inject Mock.xConfig, fOfB)]
                    }
        assertEqual
            "ceil(functional and eq(f(a), g(a)))"
            expected
            actual
    , testCase "ceil with functional composition" $ do
        -- if term is functional(non-funct, non-funct), then
        -- ceil(term and predicate and subst)
        --     = top and
        --       ceil(non-funct) and ceil(non-funct) and predicate and
        --       subst
        let expected =
                NormalForm.fromPredicates
                    [ makeCeilPredicate fOfA
                    , makeCeilPredicate fOfB
                    , makeEqualsPredicate fOfA gOfA
                    , makeEqualsPredicate (mkElemVar Mock.xConfig) fOfB
                    ]
        actual <-
            makeEvaluate
                Conditional
                    { term = Mock.functional20 fOfA fOfB
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution =
                        Substitution.wrap
                            $ Substitution.mkUnwrappedSubstitution
                                [(inject Mock.xConfig, fOfB)]
                    }
        assertEqual
            "ceil(functional(non-funct, non-funct) and eq(f(a), g(a)))"
            expected
            actual
    , testCase "Simplifies functional term, adds ceils to children" $ do
        let expected =
                NormalForm.fromPredicates
                    [ makeEqualsPredicate fOfA gOfA
                    , makeEqualsPredicate (mkElemVar Mock.xConfig) fOfB
                    , makeCeilPredicate fOfA
                    , makeCeilPredicate fOfB
                    ]
        actual <-
            makeEvaluate
                Conditional
                    { term = Mock.functional20 fOfA fOfB
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution =
                        Substitution.wrap
                            $ Substitution.mkUnwrappedSubstitution
                                [(inject Mock.xConfig, fOfB)]
                    }
        assertEqual
            ""
            expected
            actual
    , testCase "ceil with normal domain value" $ do
        -- ceil(1) = top
        let expected = NormalForm.fromPredicate fromTop_
        actual <-
            makeEvaluate
                $ Pattern.fromTermLike
                $ mkDomainValue
                    DomainValue
                        { domainValueSort = Mock.testSort
                        , domainValueChild = mkStringLiteral "a"
                        }
        assertEqual "ceil(1)" expected actual
    , testCase "ceil with list domain value" $ do
        -- ceil([a, b]) = ceil(a) and ceil(b)
        let expected =
                NormalForm.fromPredicates
                    [ makeCeilPredicate fOfA
                    , makeCeilPredicate fOfB
                    ]
        actual <-
            makeEvaluate
                Conditional
                    { term = Mock.builtinList [fOfA, fOfB]
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
        assertEqual "ceil(list)" expected actual
    , testCase "ceil of sort injection" $ do
        let expected =
                makeCeilPredicate fOfA
                    & NormalForm.fromPredicate
        actual <-
            (makeEvaluate . Pattern.fromTermLike)
                (Mock.sortInjection Mock.topSort (TermLike.markSimplified fOfA))
        assertEqual "ceil(f(a))" expected actual
    ]
    where
        fOfA :: TermLike RewritingVariableName
        fOfA = Mock.f Mock.a
        fOfB :: TermLike RewritingVariableName
        fOfB = Mock.f Mock.b
        gOfA = Mock.g Mock.a
        somethingOfA = Mock.plain10 Mock.a
        somethingOfB = Mock.plain10 Mock.b
        somethingOfAExpanded = Pattern.fromTermLike somethingOfA
        somethingOfBExpanded = Pattern.fromTermLike somethingOfB

makeCeil ::
    [Pattern RewritingVariableName] ->
    Ceil Sort (OrPattern RewritingVariableName)
makeCeil patterns =
    Ceil
        { ceilOperandSort = testSort
        , ceilResultSort = testSort
        , ceilChild = OrPattern.fromPatterns patterns
        }

evaluate ::
    Ceil Sort (OrPattern RewritingVariableName) ->
    IO NormalForm
evaluate ceil =
    testRunSimplifier mockEnv
        $ Ceil.simplify SideCondition.top ceil
    where
        mockEnv = Mock.env

makeEvaluate ::
    Pattern RewritingVariableName -> IO NormalForm
makeEvaluate = makeEvaluateWithAxioms Map.empty

makeEvaluateWithAxioms ::
    Map.Map AxiomIdentifier.AxiomIdentifier [Equation RewritingVariableName] ->
    Pattern RewritingVariableName ->
    IO NormalForm
makeEvaluateWithAxioms axiomEquations child =
    testRunSimplifier mockEnv
        $ Ceil.makeEvaluate SideCondition.top child
    where
        mockEnv = Mock.env{axiomEquations}
