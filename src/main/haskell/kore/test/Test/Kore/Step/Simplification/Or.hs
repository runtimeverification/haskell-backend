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
import           Test.Kore
                 ( sortVariableSort )

          {- Part 1: `SimplifyEvaluated` is the core function. It converts two
             `OrOfExpandedPattern` values into a simplifier that is to
             produce a single `OrOfExpandedPattern`. We run the simplifier to
             check correctness.
          -}


test_topDominates :: TestTree
test_topDominates =
  testGroup "top values override 'lower' values"
  [
    -- omission next line produces (OrOfExpandedPattern.merge middleX topOr, SimplificationProof)
    -- simplifyEvaluated middleX   topOr     `equals_` (topOr, SimplificationProof)
    -- bug: following produces `middleX`. 
    -- , simplifyEvaluated topOr    middleX    `equals_` (topOr, SimplificationProof)
    simplifyEvaluated topOr    topOr     `equals_` (topOr, SimplificationProof)
  , simplifyEvaluated topOr    bottomOr  `equals_` (topOr, SimplificationProof)
  , simplifyEvaluated bottomOr topOr     `equals_` (topOr, SimplificationProof)
  ]
    

test_bottomIsEliminated :: TestTree
test_bottomIsEliminated =
  testGroup "bottom values are eliminated"
  [
    simplifyEvaluated middleX   bottomOr  `equals_` (middleX, SimplificationProof)
  , simplifyEvaluated bottomOr  middleX   `equals_` (middleX, SimplificationProof)
  , simplifyEvaluated topOr     bottomOr  `equals_` (topOr, SimplificationProof)
  , simplifyEvaluated bottomOr  topOr     `equals_` (topOr, SimplificationProof)
  , simplifyEvaluated bottomOr  bottomOr  `equals_` (bottomOr, SimplificationProof)
  ]
    
test_middleValuesAreBothRetained :: TestTree
test_middleValuesAreBothRetained = 
  testGroup "Any other values are merged"
  [
    equals_
      (simplifyEvaluated middleX middleY)
      (OrOfExpandedPattern.merge middleX middleY, SimplificationProof)
  ]

        {- Part 2: `simplify` is just a trivial use of `simplifyEvaluated` -}

test_simplify :: TestTree
test_simplify =
  testGroup "`simplify` just calls `simplifyEvaluated`"
  [
    equals_
      (simplify           $ mkOr middleX middleY) 
      (simplifyEvaluated         middleX middleY)
  ]
  where
      mkOr first second =
        Or { orFirst = first
           , orSecond = second
           , orSort = sortVariableSort "irrelevant"
           }



        {- Part 3: The values relevant to this test -}

topOr :: OrOfExpandedPattern Object Variable
topOr = OrOfExpandedPattern.make [ExpandedPattern.top]

bottomOr :: OrOfExpandedPattern Object Variable
bottomOr = OrOfExpandedPattern.make [ExpandedPattern.bottom]


mkMiddle :: Variable Object -> OrOfExpandedPattern Object Variable
mkMiddle variable =
  OrOfExpandedPattern.make [raw]
  where
    raw = Predicated
            { term = mkVar variable
            , predicate = makeTruePredicate 
            , substitution = mempty
            }

-- QUESTION: ask Tom what a Variable is, vs. other things.
-- Should other things play any role in testing?

middleX :: OrOfExpandedPattern Object Variable
middleX = mkMiddle Mock.x
middleY :: OrOfExpandedPattern Object Variable
middleY = mkMiddle Mock.y


test_testValuesAreAsExpected :: TestTree
test_testValuesAreAsExpected =
  testGroup "check properties of test values"
  [ topOr `has_`    [ (isTop, True),  (isBottom, False) ]
  , middleX `has_`  [ (isTop, False), (isBottom, False) ]
  , bottomOr `has_` [ (isTop, False), (isBottom, True) ]
  ]

