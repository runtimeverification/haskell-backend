module Test.Kore.Step.Simplification.Ceil
    ( test_ceilSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import Data.Reflection
       ( give )

import           Kore.AST.Pure
import           Kore.ASTUtils.SmartConstructors
                 ( mkBottom, mkDomainValue, mkStringLiteral, mkTop )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Bottom_ )
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeCeilPredicate, makeEqualsPredicate,
                 makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( bottom, top )
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern, OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Pattern
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluate, simplify )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Unification.Substitution as Substitution

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools, makeSymbolOrAliasSorts )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_ceilSimplification :: [TestTree]
test_ceilSimplification = give mockSymbolOrAliasSorts
    [ testCase "Ceil - or distribution"
        -- ceil(a or b) = (top and ceil(a)) or (top and ceil(b))
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ Predicated
                    { term = mkTop
                    , predicate = makeCeilPredicate somethingOfA
                    , substitution = mempty
                    }
                , Predicated
                    { term = mkTop
                    , predicate = makeCeilPredicate somethingOfB
                    , substitution = mempty
                    }
                ]
            )
            (evaluate mockMetadataTools
                (makeCeil
                    [somethingOfAExpanded, somethingOfBExpanded]
                )
            )
        )
    , testCase "Ceil - bool operations"
        (do
            -- ceil(top) = top
            assertEqualWithExplanation "ceil(top)"
                (OrOfExpandedPattern.make
                    [ ExpandedPattern.top ]
                )
                (evaluate mockMetadataTools
                    (makeCeil
                        [ExpandedPattern.top]
                    )
                )
            -- ceil(bottom) = bottom
            assertEqualWithExplanation "ceil(bottom)"
                (OrOfExpandedPattern.make
                    []
                )
                (evaluate mockMetadataTools
                    (makeCeil
                        []
                    )
                )
        )
    , testCase "expanded Ceil - bool operations"
        (do
            -- ceil(top) = top
            assertEqualWithExplanation "ceil(top)"
                (OrOfExpandedPattern.make
                    [ ExpandedPattern.top ]
                )
                (makeEvaluate mockMetadataTools
                    (ExpandedPattern.top :: CommonExpandedPattern Object)
                )
            -- ceil(bottom) = bottom
            assertEqualWithExplanation "ceil(bottom)"
                (OrOfExpandedPattern.make
                    []
                )
                (makeEvaluate mockMetadataTools
                    (ExpandedPattern.bottom :: CommonExpandedPattern Object)
                )
        )
    , testCase "ceil with predicates and substitutions"
        -- if term is not functional, then
        -- ceil(term and predicate and subst)
        --     = top and (ceil(term) and predicate) and subst
        (assertEqualWithExplanation "ceil(something(a) and equals(f(a), g(a)))"
            (OrOfExpandedPattern.make
                [ Predicated
                    { term = mkTop
                    , predicate =
                        makeAndPredicate
                            (makeEqualsPredicate fOfA gOfA)
                            (makeCeilPredicate somethingOfA)
                    , substitution = Substitution.wrap [(Mock.x, fOfB)]
                    }
                ]
            )
            (makeEvaluate mockMetadataTools
                Predicated
                    { term = somethingOfA
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution = Substitution.wrap [(Mock.x, fOfB)]
                    }
            )
        )
    , let
        constructorTerm = Mock.constr20 somethingOfA somethingOfB
      in
        testCase "ceil with constructors"
            -- if term is a non-functional-constructor(params), then
            -- ceil(term and predicate and subst)
            --     = top and (ceil(term) and predicate) and subst
            (assertEqualWithExplanation
                "ceil(constr(something(a), something(b)) and eq(f(a), g(a)))"
                (OrOfExpandedPattern.make
                    [ Predicated
                        { term = mkTop
                        , predicate =
                            makeAndPredicate
                                (makeEqualsPredicate fOfA gOfA)
                                (makeAndPredicate
                                    (makeCeilPredicate somethingOfA)
                                    (makeCeilPredicate somethingOfB)
                                )
                        , substitution = Substitution.wrap [(Mock.x, fOfB)]
                        }
                    ]
                )
                (makeEvaluate mockMetadataTools
                    Predicated
                        { term = constructorTerm
                        , predicate = makeEqualsPredicate fOfA gOfA
                        , substitution = Substitution.wrap [(Mock.x, fOfB)]
                        }
                )
            )
    , testCase "ceil of constructors is top"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make [ExpandedPattern.top])
            (makeEvaluate mockMetadataTools
                Predicated
                    { term = Mock.constr10 Mock.a
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
            )
        )
    , testCase "ceil with functional symbols"
        -- if term is a functional(params), then
        -- ceil(term and predicate and subst)
        --     = top and (ceil(params) and predicate) and subst
        (assertEqualWithExplanation
            "ceil(functional(something(a), something(b)) and eq(f(a), g(a)))"
            (OrOfExpandedPattern.make
                [ Predicated
                    { term = mkTop
                    , predicate =
                        makeAndPredicate
                            (makeEqualsPredicate fOfA gOfA)
                            (makeAndPredicate
                                (makeCeilPredicate somethingOfA)
                                (makeCeilPredicate somethingOfB)
                            )
                    , substitution = Substitution.wrap [(Mock.x, fOfB)]
                    }
                ]
            )
            (makeEvaluate mockMetadataTools
                Predicated
                    { term = Mock.functional20 somethingOfA somethingOfB
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution = Substitution.wrap [(Mock.x, fOfB)]
                    }
            )
        )
    , testCase "ceil with function symbols"
        -- if term is a function(params), then
        -- ceil(term and predicate and subst)
        --     = top and (ceil(term) and predicate) and subst
        (assertEqualWithExplanation
            "ceil(f(a)) and eq(f(a), g(a)))"
            (OrOfExpandedPattern.make
                [ Predicated
                    { term = mkTop
                    , predicate =
                        makeAndPredicate
                            (makeEqualsPredicate fOfA gOfA)
                            (makeCeilPredicate fOfA)
                    , substitution = Substitution.wrap [(Mock.x, fOfB)]
                    }
                ]
            )
            (makeEvaluate mockMetadataTools
                Predicated
                    { term = fOfA
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution = Substitution.wrap [(Mock.x, fOfB)]
                    }
            )
        )
    , testCase "ceil with function symbols"
        -- if term is a functional(params), then
        -- ceil(term and predicate and subst)
        --     = top and (ceil(params) and predicate) and subst
        (assertEqualWithExplanation
            "ceil(f(a)) and eq(f(a), g(a)))"
            (OrOfExpandedPattern.make
                [ Predicated
                    { term = mkTop
                    , predicate =
                        makeAndPredicate
                            (makeEqualsPredicate fOfA gOfA)
                            (makeCeilPredicate fOfA)
                    , substitution = Substitution.wrap [(Mock.x, fOfB)]
                    }
                ]
            )
            (makeEvaluate mockMetadataTools
                Predicated
                    { term = fOfA
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution = Substitution.wrap [(Mock.x, fOfB)]
                    }
            )
        )
    , testCase "ceil with functional terms"
        -- if term is functional, then
        -- ceil(term and predicate and subst)
        --     = top and predicate and subst
        (assertEqualWithExplanation
            "ceil(functional and eq(f(a), g(a)))"
            (OrOfExpandedPattern.make
                [ Predicated
                    { term = mkTop
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution = Substitution.wrap [(Mock.x, fOfB)]
                    }
                ]
            )
            (makeEvaluate mockMetadataTools
                Predicated
                    { term = Mock.a
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution = Substitution.wrap [(Mock.x, fOfB)]
                    }
            )
        )
    , testCase "ceil with functional composition"
        -- if term is functional(non-funct, non-funct), then
        -- ceil(term and predicate and subst)
        --     = top and
        --       ceil(non-funct) and ceil(non-funct) and predicate and
        --       subst
        (assertEqualWithExplanation
            "ceil(functional(non-funct, non-funct) and eq(f(a), g(a)))"
            (OrOfExpandedPattern.make
                [ Predicated
                    { term = mkTop
                    , predicate =
                        makeAndPredicate
                            (makeEqualsPredicate fOfA gOfA)
                            (makeAndPredicate
                                (makeCeilPredicate fOfA)
                                (makeCeilPredicate fOfB)
                            )
                    , substitution = Substitution.wrap [(Mock.x, fOfB)]
                    }
                ]
            )
            (makeEvaluate mockMetadataTools
                Predicated
                    { term = Mock.functional20 fOfA fOfB
                    , predicate = makeEqualsPredicate fOfA gOfA
                    , substitution = Substitution.wrap [(Mock.x, fOfB)]
                    }
            )
        )
    , testCase "ceil with normal domain value"
        -- ceil(1) = top
        (assertEqualWithExplanation
            "ceil(1)"
            (OrOfExpandedPattern.make
                [ Predicated
                    { term = mkTop
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                ]
            )
            (makeEvaluate mockMetadataTools
                Predicated
                    { term =
                        mkDomainValue
                            testSort
                            (Domain.BuiltinPattern (mkStringLiteral "a"))
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
            )
        )
    , testCase "ceil with map domain value"
        -- maps assume that their keys are relatively functional, so
        -- ceil({a->b, c->d}) = ceil(b) and ceil(d)
        (assertEqualWithExplanation
            "ceil(map)"
            (OrOfExpandedPattern.make
                [ Predicated
                    { term = mkTop
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate fOfB)
                            (makeCeilPredicate gOfB)
                    , substitution = mempty
                    }
                ]
            )
            (makeEvaluate mockMetadataTools
                Predicated
                    { term =
                        Mock.builtinMap
                            [(asConcrete fOfA, fOfB), (asConcrete gOfA, gOfB)]
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
            )
        )
    , testCase "ceil with list domain value"
        -- ceil([a, b]) = ceil(a) and ceil(b)
        (assertEqualWithExplanation
            "ceil(list)"
            (OrOfExpandedPattern.make
                [ Predicated
                    { term = mkTop
                    , predicate =
                        makeAndPredicate
                            (makeCeilPredicate fOfA)
                            (makeCeilPredicate fOfB)
                    , substitution = mempty
                    }
                ]
            )
            (makeEvaluate mockMetadataTools
                Predicated
                    { term = Mock.builtinList [fOfA, fOfB]
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
            )
        )
    , testCase "ceil with set domain value"
        -- sets assume that their elements are relatively functional,
        -- so ceil({a, b}) = top
        (assertEqualWithExplanation
            "ceil(set)"
            (OrOfExpandedPattern.make [ ExpandedPattern.top ]
            )
            (makeEvaluate mockMetadataTools
                Predicated
                    { term = Mock.builtinSet [asConcrete fOfA, asConcrete fOfB]
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
            )
        )
    ]
  where
    fOfA :: StepPattern Object Variable
    fOfA = give mockSymbolOrAliasSorts $ Mock.f Mock.a
    fOfB :: StepPattern Object Variable
    fOfB = give mockSymbolOrAliasSorts $ Mock.f Mock.b
    gOfA = give mockSymbolOrAliasSorts $ Mock.g Mock.a
    gOfB = give mockSymbolOrAliasSorts $ Mock.g Mock.b
    somethingOfA = give mockSymbolOrAliasSorts $ Mock.plain10 Mock.a
    somethingOfB = give mockSymbolOrAliasSorts $ Mock.plain10 Mock.b
    somethingOfAExpanded = Predicated
        { term = somethingOfA
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    somethingOfBExpanded = Predicated
        { term = somethingOfB
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    mockSymbolOrAliasSorts =
        Mock.makeSymbolOrAliasSorts Mock.symbolOrAliasSortsMapping
    mockMetadataTools =
        Mock.makeMetadataTools
            mockSymbolOrAliasSorts
            Mock.attributesMapping
            Mock.headTypeMapping
            Mock.subsorts
    asConcrete p =
        let Just r = asConcretePurePattern p in r

makeCeil
    :: Ord (variable Object)
    => [ExpandedPattern Object variable]
    -> Ceil Object (OrOfExpandedPattern Object variable)
makeCeil patterns =
    Ceil
        { ceilOperandSort = testSort
        , ceilResultSort  = testSort
        , ceilChild       = OrOfExpandedPattern.make patterns
        }

testSort :: Sort Object
testSort =
    case mkBottom :: CommonStepPattern Object of
        Bottom_ sort -> sort
        _ -> error "unexpected"

evaluate
    ::  ( MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> Ceil level (CommonOrOfExpandedPattern level)
    -> CommonOrOfExpandedPattern level
evaluate tools ceil =
    case Ceil.simplify tools ceil of
        (result, _proof) -> result


makeEvaluate
    ::  ( MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> CommonExpandedPattern level
    -> CommonOrOfExpandedPattern level
makeEvaluate tools child =
    case Ceil.makeEvaluate tools child of
        (result, _proof) -> result
