module Test.Kore.Step.Simplification.Not
    ( test_simplifyEvaluated
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Map.Strict as Map

import           Kore.AST.Common
                 ( Variable )
import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.AST.Valid
import qualified Kore.Attribute.Symbol as Attribute
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Predicate.Predicate
                 ( Predicate )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Representation.ExpandedPattern
                 ( ExpandedPattern )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.Representation.MultiOr as MultiOr
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.Representation.PredicateSubstitution as PredicateSubstitution
import           Kore.Step.Simplification.Data
                 ( evalSimplifier, gather )
import qualified Kore.Step.Simplification.Not as Not
import qualified Kore.Step.Simplification.Simplifier as Simplifier
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution
import qualified SMT

import           Test.Kore
import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
import qualified Test.Kore.Step.MockSimplifiers as Mock
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_simplifyEvaluated :: [TestTree]
test_simplifyEvaluated =
    [ [ExpandedPattern.top] `becomes_` []
    , [] `becomes_` [ExpandedPattern.top]
    , [termX] `becomes_` [mkNot <$> termX]
    , [equalsXA] `becomes_` [notEqualsXA]
    , [substXA] `becomes_` [notEqualsXA]
    , [equalsXA, equalsXB] `becomes_` [neitherXAB]
    ]
  where
    becomes_ original expected =
        testCase "becomes" $ do
            actual <- simplifyEvaluated (MultiOr.make original)
            assertEqualWithExplanation "" (MultiOr.make expected) actual

termX :: ExpandedPattern Object Variable
termX = ExpandedPattern.fromPurePattern (mkVar Mock.x)

equalsXA :: ExpandedPattern Object Variable
equalsXA = fromPredicate equalsXA_

equalsXB :: ExpandedPattern Object Variable
equalsXB = fromPredicate equalsXB_

equalsXA_ :: Predicate Object Variable
equalsXA_ = Predicate.makeEqualsPredicate (mkVar Mock.x) Mock.a

equalsXB_ :: Predicate Object Variable
equalsXB_ = Predicate.makeEqualsPredicate (mkVar Mock.x) Mock.b

notEqualsXA :: ExpandedPattern Object Variable
notEqualsXA = fromPredicate $ Predicate.makeNotPredicate $ equalsXA_

neitherXAB :: ExpandedPattern Object Variable
neitherXAB =
    fromPredicate
    $ Predicate.makeAndPredicate
        (Predicate.makeNotPredicate equalsXA_)
        (Predicate.makeNotPredicate equalsXB_)

substXA :: ExpandedPattern Object Variable
substXA = fromSubstitution $ Substitution.unsafeWrap [(Mock.x, Mock.a)]

fromPredicate :: Predicate Object Variable -> ExpandedPattern Object Variable
fromPredicate =
    ExpandedPattern.fromPredicateSubstitution
    . PredicateSubstitution.fromPredicate

fromSubstitution
    :: Substitution Object Variable
    -> ExpandedPattern Object Variable
fromSubstitution =
    ExpandedPattern.fromPredicateSubstitution
    . PredicateSubstitution.fromSubstitution

simplifyEvaluated
    :: OrOfExpandedPattern Object Variable
    -> IO (OrOfExpandedPattern Object Variable)
simplifyEvaluated =
    SMT.runSMT SMT.defaultConfig
    . evalSimplifier emptyLogger
    . gather
    . Not.simplifyEvaluated
        mockMetadataTools
        (Mock.substitutionSimplifier mockMetadataTools)
        (Simplifier.create mockMetadataTools Map.empty)
        Map.empty

mockMetadataTools :: MetadataTools Object Attribute.Symbol
mockMetadataTools =
    Mock.makeMetadataTools
        Mock.attributesMapping
        Mock.headTypeMapping
        Mock.sortAttributesMapping
        Mock.subsorts
        Mock.headSortsMapping
