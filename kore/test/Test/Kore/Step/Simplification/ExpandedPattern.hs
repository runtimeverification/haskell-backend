module Test.Kore.Step.Simplification.ExpandedPattern
    ( test_simplifyPredicateBranch
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit

import qualified Data.Map as Map

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.Representation.ExpandedPattern
                 ( CommonExpandedPattern, Predicated (..) )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern )
import           Kore.Step.Simplification.Data hiding
                 ( runSimplifier )
import qualified Kore.Step.Simplification.ExpandedPattern as Simplify
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           SMT
                 ( SMT )
import qualified SMT

import           Test.Kore
import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools )
import qualified Test.Kore.Step.MockSimplifiers as Mock
import qualified Test.Kore.Step.MockSymbols as Mock

test_simplifyPredicateBranch :: [TestTree]
test_simplifyPredicateBranch =
    [ testCase "predicate = \\bottom" $ do
        let expect = mempty
            original = ExpandedPattern.bottomPredicate { term = mkTop_ }
        actual <- simplifyPredicateBranch original
        assertEqual "Expected empty result" expect actual
    , testCase "term = \\bottom" $ do
        let expect = mempty
            original = ExpandedPattern.topPredicate { term = mkBottom_ }
        actual <- simplifyPredicateBranch original
        assertEqual "Expected empty result" expect actual
    ]

mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools
        Mock.attributesMapping
        Mock.headTypeMapping
        Mock.sortAttributesMapping
        Mock.subsorts

simplifyPredicateBranch
    :: CommonExpandedPattern Object
    -> IO (CommonOrOfExpandedPattern Object)
simplifyPredicateBranch =
    runSMT
    . evalSimplifier emptyLogger
    . gather
    . Simplify.simplifyPredicateBranch
        mockMetadataTools
        (Mock.substitutionSimplifier mockMetadataTools)
        (Simplifier.create mockMetadataTools Map.empty)
        Map.empty

-- | Run an 'SMT' computation with the default configuration.
runSMT :: SMT a -> IO a
runSMT = SMT.runSMT SMT.defaultConfig
