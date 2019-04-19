module Test.Kore.Step.Simplification.Not
    ( test_simplifyEvaluated
    ) where

import Test.Tasty

import qualified Data.Function as Function

import           Kore.AST.Common
                 ( Variable )
import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.AST.Valid
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
import qualified Kore.Step.Simplification.Not as Not
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution

import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSymbols as Mock
import qualified Test.Terse as Terse

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
    becomes_ =
        Function.on (Terse.equals_ . simplifyEvaluated) MultiOr.make

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
    -> OrOfExpandedPattern Object Variable
simplifyEvaluated = fst . Not.simplifyEvaluated
