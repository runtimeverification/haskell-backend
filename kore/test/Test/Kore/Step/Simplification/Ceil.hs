module Test.Kore.Step.Simplification.Ceil
    ( test_ceilSimplification
    ) where

import Test.Tasty

import qualified Data.Map as Map

import qualified Data.Sup as Sup
import qualified Kore.Builtin.AssociativeCommutative as Ac
import qualified Kore.Domain.Builtin as Domain
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike as TermLike
import Kore.Predicate.Predicate
    ( makeAndPredicate
    , makeCeilPredicate
    , makeEqualsPredicate
    , makeTruePredicate
    )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
    ( AxiomIdentifier (..)
    )
import qualified Kore.Step.Simplification.Ceil as Ceil
    ( makeEvaluate
    , simplify
    )
import Kore.Step.Simplification.Simplify
import qualified Kore.Step.Simplification.Simplify as AttemptedAxiomResults
    ( AttemptedAxiomResults (..)
    )
import qualified Kore.Step.Simplification.Simplify as AttemptedAxiom
    ( AttemptedAxiom (..)
    )
import qualified Kore.Unification.Substitution as Substitution
import Kore.Variables.Fresh
    ( FreshVariable
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import Test.Kore.Builtin.Builtin
    ( emptyNormalizedSet
    )
import Test.Kore.Step.MockSymbols
    ( testSort
    )
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Kore.With
import Test.Tasty.HUnit.Ext

test_ceilSimplification :: [TestTree]
test_ceilSimplification =
    [ testCase "Ceil - or distribution" $ do
        -- ceil(a or b) = (top and ceil(a)) or (top and ceil(b))
        let
            expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate = makeCeilPredicate somethingOfA
                    , substitution = mempty
                    }
                , Conditional
                    { term = mkTop_
                    , predicate = makeCeilPredicate somethingOfB
                    , substitution = mempty
                    }
                ]
        actual <- evaluate
            (makeCeil
                [somethingOfAExpanded, somethingOfBExpanded]
            )
        assertEqual "" expected actual
    , testCase "Ceil - bool operations"
        (do
            -- ceil(top) = top
            actual1 <- evaluate
                (makeCeil
                    [Pattern.top]
                )
            assertEqual "ceil(top)"
                (OrPattern.fromPatterns
                    [ Pattern.top ]
                )
                actual1
            -- ceil(bottom) = bottom
            actual2 <- evaluate
                (makeCeil
                    []
                )
            assertEqual "ceil(bottom)"
                (OrPattern.fromPatterns
                    []
                )
                actual2
        )
    , testCase "expanded Ceil - bool operations"
        (do
            -- ceil(top) = top
            actual1 <- makeEvaluate Pattern.top
            assertEqual "ceil(top)"
                (OrPattern.fromPatterns
                    [ Pattern.top ]
                )
                actual1
            -- ceil(bottom) = bottom
            actual2 <- makeEvaluate Pattern.bottom
            assertEqual "ceil(bottom)"
                (OrPattern.fromPatterns
                    []
                )
                actual2
        )
    , testCase "ceil with predicates and substitutions" $ do
        -- if term is not functional, then
        -- ceil(term and predicate and subst)
        --     = top and (ceil(term) and predicate) and subst
        let
            expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate =
                        makeAndPredicate
                        (makeCeilPredicate somethingOfA)
                        (makeEqualsPredicate fOfA gOfA)
                    , substitution =
                        Substitution.unsafeWrap [(ElemVar Mock.x, fOfB)]
                    }
                ]
        actual <- makeEvaluate
            Conditional
                { term = somethingOfA
                , predicate = makeEqualsPredicate fOfA gOfA
                , substitution = Substitution.wrap [(ElemVar Mock.x, fOfB)]
                }
        assertEqual "ceil(something(a) and equals(f(a), g(a)))"
            expected
            actual
    , let
        constructorTerm = Mock.constr20 somethingOfA somethingOfB
      in
        testCase "ceil with constructors" $ do
            -- if term is a non-functional-constructor(params), then
            -- ceil(term and predicate and subst)
            --     = top and (ceil(term) and predicate) and subst
            let
                expected = OrPattern.fromPatterns
                    [ Conditional
                        { term = mkTop_
                        , predicate =
                            makeAndPredicate
                                (makeAndPredicate
                                    (makeCeilPredicate somethingOfA)
                                    (makeCeilPredicate somethingOfB)
                                )
                                (makeEqualsPredicate fOfA gOfA)
                        , substitution =
                            Substitution.unsafeWrap [(ElemVar Mock.x, fOfB)]
                        }
                    ]
            actual <- makeEvaluate
                Conditional
                    { term = constructorTerm
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution = Substitution.wrap [(ElemVar Mock.x, fOfB)]
                    }
            assertEqual
                "ceil(constr(something(a), something(b)) and eq(f(a), g(a)))"
                expected
                actual
    , testCase "ceil of constructors is top" $ do
        let
            expected = OrPattern.fromPatterns [Pattern.top]
        actual <- makeEvaluate
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
        let
            expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate =
                        makeAndPredicate
                            (makeAndPredicate
                                (makeCeilPredicate somethingOfA)
                                (makeCeilPredicate somethingOfB)
                            )
                            (makeEqualsPredicate fOfA gOfA)
                    , substitution =
                        Substitution.unsafeWrap [(ElemVar Mock.x, fOfB)]
                    }
                ]
        actual <- makeEvaluate
            Conditional
                { term = Mock.functional20 somethingOfA somethingOfB
                , predicate = makeEqualsPredicate fOfA gOfA
                , substitution = Substitution.wrap [(ElemVar Mock.x, fOfB)]
                }
        assertEqual
            "ceil(functional(something(a), something(b)) and eq(f(a), g(a)))"
            expected
            actual
    , testCase "ceil with function symbols" $ do
        -- if term is a function(params), then
        -- ceil(term and predicate and subst)
        --     = top and (ceil(term) and predicate) and subst
        let
            expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate fOfA)
                            (makeEqualsPredicate fOfA gOfA)
                    , substitution =
                        Substitution.unsafeWrap [(ElemVar Mock.x, fOfB)]
                    }
                ]
        actual <- makeEvaluate
            Conditional
                { term = fOfA
                , predicate = makeEqualsPredicate fOfA gOfA
                , substitution = Substitution.wrap [(ElemVar Mock.x, fOfB)]
                }
        assertEqual
            "ceil(f(a)) and eq(f(a), g(a)))"
            expected
            actual
    , testCase "ceil with functional terms" $ do
        -- if term is functional, then
        -- ceil(term and predicate and subst)
        --     = top and predicate and subst
        let
            expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution =
                        Substitution.unsafeWrap [(ElemVar Mock.x, fOfB)]
                    }
                ]
        actual <- makeEvaluate
            Conditional
                { term = Mock.a
                , predicate = makeEqualsPredicate fOfA gOfA
                , substitution = Substitution.wrap [(ElemVar Mock.x, fOfB)]
                }
        assertEqual
            "ceil(functional and eq(f(a), g(a)))"
            expected
            actual
    , testCase "ceil with evaluated functional terms" $ do
        -- if term is functional, then
        -- ceil(term and predicate and subst)
        --     = top and predicate and subst
        let
            expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution =
                        Substitution.unsafeWrap [(ElemVar Mock.x, fOfB)]
                    }
                ]
        actual <- makeEvaluate
            Conditional
                { term = mkEvaluated Mock.a
                , predicate = makeEqualsPredicate fOfA gOfA
                , substitution = Substitution.wrap [(ElemVar Mock.x, fOfB)]
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
        let
            expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate =
                        makeAndPredicate
                            (makeAndPredicate
                                (makeCeilPredicate fOfA)
                                (makeCeilPredicate fOfB)
                            )
                            (makeEqualsPredicate fOfA gOfA)
                    , substitution =
                        Substitution.unsafeWrap [(ElemVar Mock.x, fOfB)]
                    }
                ]
        actual <- makeEvaluate
            Conditional
                { term = Mock.functional20 fOfA fOfB
                , predicate = makeEqualsPredicate fOfA gOfA
                , substitution = Substitution.wrap [(ElemVar Mock.x, fOfB)]
                }
        assertEqual
            "ceil(functional(non-funct, non-funct) and eq(f(a), g(a)))"
            expected
            actual
    , testCase "ceil with axioms" $ do
        -- if term is functional(non-funct, non-funct), then
        -- ceil(term and predicate and subst)
        --     = top and
        --       ceil(non-funct) and ceil(non-funct) and predicate and
        --       subst
        let
            expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate =
                        makeAndPredicate
                            (makeEqualsPredicate Mock.a Mock.cf)
                            (makeEqualsPredicate fOfA gOfA)
                    , substitution =
                        Substitution.unsafeWrap [(ElemVar Mock.x, fOfB)]
                    }
                ]
        actual <- makeEvaluateWithAxioms
            (Map.singleton
                (AxiomIdentifier.Ceil
                    (AxiomIdentifier.Application Mock.fId)
                )
                (appliedMockEvaluator
                    Conditional
                        { term = mkTop_
                        , predicate = makeEqualsPredicate Mock.a Mock.cf
                        , substitution = mempty
                        }
                )
            )
            Conditional
                { term = Mock.functional20 fOfA fOfB
                , predicate = makeEqualsPredicate fOfA gOfA
                , substitution = Substitution.wrap [(ElemVar Mock.x, fOfB)]
                }
        assertEqual
            "ceil(functional(non-funct, non-funct) and eq(f(a), g(a)))"
            expected
            actual
    , testCase "ceil with normal domain value" $ do
        -- ceil(1) = top
        let
            expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                ]
        actual <- makeEvaluate
            $ Pattern.fromTermLike
            $ mkDomainValue DomainValue
                { domainValueSort = Mock.testSort
                , domainValueChild = mkStringLiteral "a"
                }
        assertEqual "ceil(1)" expected actual
    , testGroup "Builtin.Map"
        [ testCase "concrete partial keys" $ do
            -- maps assume that their keys are relatively functional, so
            -- ceil({a->b, c->d}) = ceil(b) and ceil(d)
            let original = Mock.builtinMap [(fOfA, fOfB), (gOfA, gOfB)]
                expected =
                    OrPattern.fromPattern . Pattern.fromPredicate
                    . Predicate.fromPredicate
                    $ makeAndPredicate
                        (makeCeilPredicate fOfB)
                        (makeCeilPredicate gOfB)
            actual <- makeEvaluate $ Pattern.fromTermLike original
            assertEqual "" expected actual
        , testCase "abstract keys" $ do
            let original =
                    Mock.builtinMap [(mkElemVar Mock.x, mkElemVar Mock.y)]
                expected = OrPattern.top
            actual <- makeEvaluate $ Pattern.fromTermLike original
            assertEqual "" expected actual
        , testCase "abstract keys with frame" $ do
            let original =
                    Mock.framedMap
                        [(mkElemVar Mock.x, mkElemVar Mock.y)]
                        [Mock.m]
                expected =
                    OrPattern.fromPattern . Pattern.fromPredicate
                    . Predicate.fromPredicate . makeCeilPredicate
                    $ Mock.framedMap
                        [(mkElemVar Mock.x, mkElemVar Mock.y)]
                        [Mock.m]
            actual <- makeEvaluate $ Pattern.fromTermLike original
            assertEqual "" expected actual
        ]
    , testCase "ceil with list domain value" $ do
        -- ceil([a, b]) = ceil(a) and ceil(b)
        let
            expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate fOfA)
                            (makeCeilPredicate fOfB)
                    , substitution = mempty
                    }
                ]
        actual <- makeEvaluate
            Conditional
                { term = Mock.builtinList [fOfA, fOfB]
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertEqual "ceil(list)" expected actual
    , testCase "ceil with concrete set domain value" $ do
        -- sets assume that their concrete elements are relatively functional,
        -- so ceil({a, b}) = top
        let
            expected = OrPattern.fromPatterns [ Pattern.top ]
        actual <- makeEvaluate
            Conditional
                { term = Mock.builtinSet [asConcrete' fOfA, asConcrete' fOfB]
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertEqual "ceil(set)" expected actual
    , testCase "ceil with element variable" $ do
        let
            expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate = makeCeilPredicate fOfX
                    , substitution = mempty
                    }
                ]
        actual <- makeEvaluate
            Conditional
                { term = asInternalSet $
                    emptyNormalizedSet `with` VariableElement fOfX
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertEqual "ceil(set)" expected actual
    , testCase "ceil with opaque set" $ do
        let
            expected = OrPattern.fromPatterns
                [ Conditional
                    { term = mkTop_
                    , predicate = makeCeilPredicate fOfXset
                    , substitution = mempty
                    }
                ]
        actual <- makeEvaluate
            Conditional
                { term = asInternalSet $
                    emptyNormalizedSet `with` OpaqueSet fOfXset
                , predicate = makeTruePredicate
                , substitution = mempty
                }
        assertEqual "ceil(set)" expected actual
    ]
  where
    fOfA :: TermLike Variable
    fOfA = Mock.f Mock.a
    fOfB :: TermLike Variable
    fOfB = Mock.f Mock.b
    gOfA = Mock.g Mock.a
    gOfB = Mock.g Mock.b
    fOfX :: TermLike Variable
    fOfX = Mock.f (mkElemVar Mock.x)
    fOfXset :: TermLike Variable
    fOfXset = Mock.fSet (mkElemVar Mock.xSet)
    somethingOfA = Mock.plain10 Mock.a
    somethingOfB = Mock.plain10 Mock.b
    somethingOfAExpanded = Conditional
        { term = somethingOfA
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    somethingOfBExpanded = Conditional
        { term = somethingOfB
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    asConcrete' p = let Just r = TermLike.asConcrete p in r
    asInternalSet =
        Ac.asInternal Mock.metadataTools Mock.setSort . Domain.wrapAc

appliedMockEvaluator
    :: Pattern Variable -> BuiltinAndAxiomSimplifier
appliedMockEvaluator result =
    BuiltinAndAxiomSimplifier
    $ mockEvaluator
    $ AttemptedAxiom.Applied AttemptedAxiomResults
        { results = OrPattern.fromPatterns
            [Test.Kore.Step.Simplification.Ceil.mapVariables result]
        , remainders = OrPattern.fromPatterns []
        }

mockEvaluator
    :: MonadSimplify simplifier
    => AttemptedAxiom variable
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -> TermLike variable
    -> Predicate variable
    -> simplifier (AttemptedAxiom variable)
mockEvaluator evaluation _ _ _ _ = return evaluation

mapVariables
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Ord variable
        )
    => Pattern Variable
    -> Pattern variable
mapVariables =
    Pattern.mapVariables $ \v ->
        fromVariable v { variableCounter = Just (Sup.Element 1) }

makeCeil
    :: Ord variable
    => [Pattern variable]
    -> Ceil Sort (OrPattern variable)
makeCeil patterns =
    Ceil
        { ceilOperandSort = testSort
        , ceilResultSort  = testSort
        , ceilChild       = OrPattern.fromPatterns patterns
        }

evaluate
    :: Ceil Sort (OrPattern Variable)
    -> IO (OrPattern Variable)
evaluate ceil =
    runSimplifier mockEnv
    $ Ceil.simplify Predicate.top ceil
  where
    mockEnv = Mock.env

makeEvaluate
    :: Pattern Variable
    -> IO (OrPattern Variable)
makeEvaluate = makeEvaluateWithAxioms Map.empty

makeEvaluateWithAxioms
    :: BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    -> Pattern Variable
    -> IO (OrPattern Variable)
makeEvaluateWithAxioms axiomIdToSimplifier child =
    runSimplifier mockEnv
    $ Ceil.makeEvaluate Predicate.top child
  where
    mockEnv = Mock.env { simplifierAxioms = axiomIdToSimplifier }
