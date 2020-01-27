module Test.Kore.Log.WarnSimplificationWithRemainder
    ( test_instance_Table_WarnSimplificationWithRemainder
    ) where

import Test.Tasty

import qualified Kore.Internal.Condition as Condition
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.TermLike
import Kore.Log.WarnSimplificationWithRemainder

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.SQL

test_instance_Table_WarnSimplificationWithRemainder :: TestTree
test_instance_Table_WarnSimplificationWithRemainder =
    testTable @WarnSimplificationWithRemainder [warn1, warn2]

warn1, warn2 :: WarnSimplificationWithRemainder
warn1 =
    WarnSimplificationWithRemainder
        { inputPattern = term1
        , sideCondition = SideCondition.top
        , results = Results results1
        , remainders = Remainders remainders1
        }
warn2 =
    WarnSimplificationWithRemainder
        { inputPattern = term2
        , sideCondition = SideCondition.top
        , results = Results results2
        , remainders = Remainders remainders2
        }

term1, term2 :: TermLike Variable
term1 = Mock.f Mock.a
term2 = Mock.f Mock.b

results1, results2 :: OrPattern Variable
results1 =
    OrPattern.fromPattern $ Pattern.andCondition
        (Pattern.fromTermLike Mock.a)
        (Condition.fromPredicate predicate1)
results2 =
    OrPattern.fromPattern $ Pattern.andCondition
        (Pattern.fromTermLike Mock.b)
        (Condition.fromPredicate predicate2)

predicate1, predicate2 :: Predicate Variable
predicate1 = makeEqualsPredicate_ (Mock.g Mock.a) (Mock.h Mock.a)
predicate2 = makeEqualsPredicate_ (Mock.g Mock.b) (Mock.h Mock.b)

remainders1, remainders2 :: OrPattern Variable
remainders1 =
    OrPattern.fromPattern $ Pattern.andCondition
        (Pattern.fromTermLike Mock.a)
        (Condition.fromPredicate $ makeNotPredicate predicate1)
remainders2 =
    OrPattern.fromPattern $ Pattern.andCondition
        (Pattern.fromTermLike Mock.b)
        (Condition.fromPredicate $ makeNotPredicate predicate2)
