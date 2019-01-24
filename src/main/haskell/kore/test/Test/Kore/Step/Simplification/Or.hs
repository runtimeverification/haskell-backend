module Test.Kore.Step.Simplification.Or where

import           Kore.Step.Simplification.Or
                 ( simplify, simplifyEvaluated )

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.HUnit.Extensions
import Test.Terse

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Data.Set as Set
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeCeilPredicate, makeEqualsPredicate,
                 makeFalsePredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, Predicated (..), isTop, isBottom)
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( bottom, top, allVariables )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern , extractPatterns )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make, merge )
import           Kore.Step.Simplification.Data
                 ( evalSimplifier, SimplificationProof )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Unification.Substitution as Substitution
import qualified SMT

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools )
import qualified Test.Kore.Step.MockSimplifiers as Mock
import           Test.Kore.Step.MockSymbols
                 ( testSort )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )

{- Part 1: `SimplifyEvaluated` is the core function. It converts two
   `OrOfExpandedPattern` values into a simplifier that is to
   produce a single `OrOfExpandedPattern`. We run the simplifier to
   check correctness.
-}

{- Part 1a: Handling of the easy cases: Top and Bottom values -}

topOr :: OrOfExpandedPattern Object Variable
topOr = OrOfExpandedPattern.make [ExpandedPattern.top]

middle :: OrOfExpandedPattern Object Variable
middle =
  OrOfExpandedPattern.make [raw]
  where
    raw = Predicated
            { term = mkVar Mock.y
            , predicate = makeTruePredicate 
            , substitution = mempty
            }


test_testValuesAreAsExpected :: TestTree
test_testValuesAreAsExpected =
  testGroup "check properties of test values"
  [ topOr `has`  [ (isTop, True),  (isBottom, False) ]
  , middle `has` [ (isTop, False), (isBottom, False) ]
  ]


test_topIsEliminated :: TestTree
test_topIsEliminated =
  testGroup "top values are eliminated"
  [
    -- omission next line produces (OrOfExpandedPattern.merge middle topOr, SimplificationProof)
    simplifyEvaluated middle topOr  `equals_` (topOr, SimplificationProof)
    -- bug: following produces `middle`. 
  , simplifyEvaluated topOr  middle `equals_` (topOr, SimplificationProof)
  , simplifyEvaluated topOr  topOr  `equals_` (topOr, SimplificationProof)
  ]
    







-- equal :: HasCallStack => Eq a => Show a => a -> a -> TestTree
-- equal actual expected =
--   testCase "equality" $ do
--     assertEqual "" expected actual

-- test_simplify :: [TestTree]
-- test_simplify =
--     [
--       equal proof SimplificationProof
--     , equal (map ExpandedPattern.allVariables (extractPatterns simplified)) $ [Set.empty]
--     ]
--     where
--       raw_variable :: Variable Object
--       raw_variable = Mock.y

-- --      (simplified, proof) :: ( OrOfExpandedPattern Object Variable , SimplificationProof Object)
--       (simplified, proof) = simplify raw_variable
