module Test.Kore.Log.DebugSkipSimplification
    ( test_instance_Table_DebugSkipSimplification
    ) where

import Prelude.Kore

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
import Kore.Log.DebugSkipSimplification
import Kore.Step.EqualityPattern
    ( EqualityRule (..)
    , equalityPattern
    )

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.SQL

test_instance_Table_DebugSkipSimplification :: TestTree
test_instance_Table_DebugSkipSimplification =
    testTable @DebugSkipSimplification [warn1, warn2]

warn1, warn2 :: DebugSkipSimplification
warn1 =
    DebugSkipSimplification
        { inputPattern = term1
        , sideCondition = SideCondition.top
        , remainders = Remainders remainders1
        , rule = rule1
        }
warn2 =
    DebugSkipSimplification
        { inputPattern = term2
        , sideCondition = SideCondition.top
        , remainders = Remainders remainders2
        , rule = rule2
        }

term1, term2 :: TermLike Variable
term1 = Mock.f Mock.a
term2 = Mock.f Mock.b

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

rule1, rule2 :: EqualityRule Variable
rule1 = EqualityRule $ equalityPattern term1 Mock.a
rule2 = EqualityRule $ equalityPattern term2 Mock.b
