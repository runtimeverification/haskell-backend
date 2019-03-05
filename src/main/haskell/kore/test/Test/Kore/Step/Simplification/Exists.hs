module Test.Kore.Step.Simplification.Exists
    ( test_existsSimplification
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Map as Map

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Predicate.Predicate
                 ( makeCeilPredicate, makeEqualsPredicate, makeExistsPredicate,
                 makeTruePredicate )
import           Kore.Step.Representation.ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern, Predicated (..) )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
                 ( bottom, top )
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern, OrOfExpandedPattern )
import qualified Kore.Step.Representation.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import qualified Kore.Step.Simplification.Exists as Exists
                 ( makeEvaluate, simplify )
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Unification.Substitution as Substitution
import qualified SMT

import           Test.Kore
import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools )
import qualified Test.Kore.Step.MockSimplifiers as Mock
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_existsSimplification :: [TestTree]
test_existsSimplification =
    [ testCase "Exists - or distribution" $ do
        -- exists(a or b) = exists(a) or exists(b)
        let expect =
                OrOfExpandedPattern.make
                    [ Predicated
                        { term = mkExists Mock.x something1OfX
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    , Predicated
                        { term = mkExists Mock.x something2OfX
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
        actual <-
            evaluate mockMetadataTools
                (makeExists
                    Mock.x
                    [something1OfXExpanded, something2OfXExpanded]
                )
        assertEqualWithExplanation "" expect actual

    , testGroup "Exists - Predicates"
        [ testCase "Top" $ do
            let expect = OrOfExpandedPattern.make [ ExpandedPattern.top ]
            actual <-
                evaluate mockMetadataTools
                    (makeExists
                        Mock.x
                        [ExpandedPattern.top]
                    )
            assertEqualWithExplanation "" expect actual

        , testCase "Bottom" $ do
            let expect = OrOfExpandedPattern.make []
            actual <-evaluate mockMetadataTools (makeExists Mock.x [])
            assertEqualWithExplanation "" expect actual

        , testCase "Expanded Top" $ do
            let expect = OrOfExpandedPattern.make [ ExpandedPattern.top ]
            actual <-
                makeEvaluate mockMetadataTools
                    Mock.x
                    (ExpandedPattern.top :: CommonExpandedPattern Object)
            assertEqualWithExplanation "" expect actual

        , testCase "Expanded Bottom" $ do
            let expect = OrOfExpandedPattern.make []
            actual <-
                makeEvaluate mockMetadataTools
                    Mock.x
                    (ExpandedPattern.bottom :: CommonExpandedPattern Object)
            assertEqualWithExplanation "" expect actual
        ]

    , testCase "exists applies substitution if possible" $ do
        -- exists x . (t(x) and p(x) and [x = alpha, others])
        --    = t(alpha) and p(alpha) and [others]
        let expect =
                OrOfExpandedPattern.make
                    [ Predicated
                        { term = Mock.f gOfA
                        , predicate =
                            makeCeilPredicate (Mock.h gOfA)
                        , substitution = Substitution.unsafeWrap
                            [(Mock.y, fOfA)]
                        }
                    ]
        actual <-
            makeEvaluate mockMetadataTools
                Mock.x
                Predicated
                    { term = Mock.f (mkVar Mock.x)
                    , predicate = makeCeilPredicate (Mock.h (mkVar Mock.x))
                    , substitution =
                        Substitution.wrap [(Mock.x, gOfA), (Mock.y, fOfA)]
                    }
        assertEqualWithExplanation "exists with substitution" expect actual

    , testCase "exists disappears if variable not used" $ do
        -- exists x . (t and p and s)
        --    = t and p and s
        --    if t, p, s do not depend on x.
        let expect =
                OrOfExpandedPattern.make
                    [ Predicated
                        { term = fOfA
                        , predicate = makeCeilPredicate gOfA
                        , substitution = mempty
                        }
                    ]
        actual <-
            makeEvaluate mockMetadataTools
                Mock.x
                Predicated
                    { term = fOfA
                    , predicate = makeCeilPredicate gOfA
                    , substitution = mempty
                    }
        assertEqualWithExplanation "exists with substitution" expect actual

    , testCase "exists applied on term if not used elsewhere" $ do
        -- exists x . (t(x) and p and s)
        --    = (exists x . t(x)) and p and s
        --    if p, s do not depend on x.
        let expect =
                OrOfExpandedPattern.make
                    [ Predicated
                        { term = mkExists Mock.x fOfX
                        , predicate = makeCeilPredicate gOfA
                        , substitution = mempty
                        }
                    ]
        actual <-
            makeEvaluate mockMetadataTools
                Mock.x
                Predicated
                    { term = fOfX
                    , predicate = makeCeilPredicate gOfA
                    , substitution = mempty
                    }
        assertEqualWithExplanation "exists on term" expect actual

    , testCase "exists applied on predicate if not used elsewhere" $ do
        -- exists x . (t and p(x) and s)
        --    = t and (exists x . p(x)) and s
        --    if t, s do not depend on x.
        let expect =
                OrOfExpandedPattern.make
                    [ Predicated
                        { term = fOfA
                        , predicate =
                            makeExistsPredicate Mock.x (makeCeilPredicate fOfX)
                        , substitution = mempty
                        }
                    ]
        actual <-
            makeEvaluate mockMetadataTools
                Mock.x
                Predicated
                    { term = fOfA
                    , predicate = makeCeilPredicate fOfX
                    , substitution = mempty
                    }
        assertEqualWithExplanation "exists on predicate" expect actual

    , testCase "exists moves substitution above" $ do
        -- exists x . (t(x) and p(x) and s)
        --    = exists x . (t(x) and p(x)) and Top and s
        --    if s do not depend on x.
        let expect =
                OrOfExpandedPattern.make
                    [ Predicated
                        { term =
                            mkExists Mock.x (mkAnd fOfX (mkEquals_ fOfX gOfA))
                        , predicate = makeTruePredicate
                        , substitution = Substitution.wrap [(Mock.y, hOfA)]
                        }
                    ]
        actual <-
            makeEvaluate mockMetadataTools
                Mock.x
                Predicated
                    { term = fOfX
                    , predicate = makeEqualsPredicate fOfX gOfA
                    , substitution = Substitution.wrap [(Mock.y, hOfA)]
                    }
        assertEqualWithExplanation "exists moves substitution" expect actual

    , testCase "exists reevaluates" $ do
        -- exists x . (top and (f(x) = f(g(a)) and [x=g(a)])
        --    = top.s
        let expect = OrOfExpandedPattern.make [ ExpandedPattern.top ]
        actual <-
            makeEvaluate mockMetadataTools
                Mock.x
                Predicated
                    { term = mkTop_
                    , predicate = makeEqualsPredicate fOfX (Mock.f gOfA)
                    , substitution = Substitution.wrap [(Mock.x, gOfA)]
                    }
        assertEqualWithExplanation "exists reevaluates" expect actual
    ]
  where
    fOfA = Mock.f Mock.a
    fOfX = Mock.f (mkVar Mock.x)
    gOfA = Mock.g Mock.a
    hOfA = Mock.h Mock.a
    something1OfX = Mock.plain10 (mkVar Mock.x)
    something2OfX = Mock.plain11 (mkVar Mock.x)
    something1OfXExpanded = Predicated
        { term = something1OfX
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    something2OfXExpanded = Predicated
        { term = something2OfX
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    mockMetadataTools =
        Mock.makeMetadataTools
            Mock.attributesMapping
            Mock.headTypeMapping
            Mock.sortAttributesMapping
            Mock.subsorts

makeExists
    :: Ord (variable Object)
    => variable Object
    -> [ExpandedPattern Object variable]
    -> Exists Object variable (OrOfExpandedPattern Object variable)
makeExists variable patterns =
    Exists
        { existsSort = testSort
        , existsVariable = variable
        , existsChild = OrOfExpandedPattern.make patterns
        }

testSort :: Sort Object
testSort =
    SortActualSort SortActual
        { sortActualName  = Id "testSort" AstLocationTest
        , sortActualSorts = []
        }

evaluate
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -> Exists level Variable (CommonOrOfExpandedPattern level)
    -> IO (CommonOrOfExpandedPattern level)
evaluate tools exists =
    (<$>) fst
    $ SMT.runSMT SMT.defaultConfig
    $ evalSimplifier emptyLogger noRepl
    $ Exists.simplify
        tools
        (Mock.substitutionSimplifier tools)
        (Simplifier.create tools Map.empty)
        Map.empty
        exists

makeEvaluate
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -> Variable level
    -> CommonExpandedPattern level
    -> IO (CommonOrOfExpandedPattern level)
makeEvaluate tools variable child =
    (<$>) fst
    $ SMT.runSMT SMT.defaultConfig
    $ evalSimplifier emptyLogger noRepl
    $ Exists.makeEvaluate
        tools
        (Mock.substitutionSimplifier tools)
        (Simplifier.create tools Map.empty)
        Map.empty
        variable
        child
