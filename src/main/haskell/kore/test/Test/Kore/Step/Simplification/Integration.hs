module Test.Kore.Step.Simplification.Integration
    (test_simplificationIntegration
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import qualified Data.Map as Map
import           Data.Reflection
                 ( give )

import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkAnd, mkBottom, mkCeil, mkExists, mkNot, mkOr, mkTop,
                 mkVar )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), top )
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
                 ( simplify )
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools, makeSymbolOrAliasSorts )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_simplificationIntegration :: [TestTree]
test_simplificationIntegration = give mockSymbolOrAliasSorts
    [ testCase "owise condition - main case"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make [])
            (evaluate
                mockMetadataTools
                ExpandedPattern
                    { term =
                        -- Use the exact form we expect from an owise condition
                        -- for f(constr10(x)) = something
                        --     f(x) = something-else [owise]
                        mkAnd
                            (mkNot
                                (mkOr
                                    (mkExists Mock.x
                                        (mkAnd
                                            mkTop
                                            (mkAnd
                                                (mkCeil
                                                    (mkAnd
                                                        (Mock.constr10
                                                            (mkVar Mock.x)
                                                        )
                                                        (Mock.constr10 Mock.a)
                                                    )
                                                )
                                                mkTop
                                            )
                                        )
                                    )
                                    mkBottom
                                )
                            )
                            mkTop
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
            )
        )
    , testCase "owise condition - owise case"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make [ExpandedPattern.top])
            (evaluate
                mockMetadataTools
                ExpandedPattern
                    { term =
                        -- Use the exact form we expect from an owise condition
                        -- for f(constr10(x)) = something
                        --     f(x) = something-else [owise]
                        mkAnd
                            (mkNot
                                (mkOr
                                    (mkExists Mock.x
                                        (mkAnd
                                            mkTop
                                            (mkAnd
                                                (mkCeil
                                                    (mkAnd
                                                        (Mock.constr10
                                                            (mkVar Mock.x)
                                                        )
                                                        (Mock.constr11 Mock.a)
                                                    )
                                                )
                                                mkTop
                                            )
                                        )
                                    )
                                    mkBottom
                                )
                            )
                            mkTop
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
            )
        )
    ]
  where
    mockSymbolOrAliasSorts = Mock.makeSymbolOrAliasSorts Mock.symbolOrAliasSortsMapping
    mockMetadataTools =
        Mock.makeMetadataTools
            mockSymbolOrAliasSorts Mock.attributesMapping Mock.subsorts

evaluate
    :: MetadataTools Object StepperAttributes
    -> CommonExpandedPattern Object
    -> CommonOrOfExpandedPattern Object
evaluate tools patt =
    fst $ evalSimplifier $
        ExpandedPattern.simplify
            tools
            (Simplifier.create tools Map.empty)
            patt
