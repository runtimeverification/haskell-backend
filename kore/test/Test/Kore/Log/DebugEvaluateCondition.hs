module Test.Kore.Log.DebugEvaluateCondition (
    test_instance_Table_DebugEvaluateCondition,
) where

import Data.List (
    inits,
 )
import Kore.Internal.Predicate
import Kore.Internal.TermLike
import Kore.Log.DebugEvaluateCondition
import Prelude.Kore
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.SQL
import Test.Tasty

test_instance_Table_DebugEvaluateCondition :: TestTree
test_instance_Table_DebugEvaluateCondition =
    testTable @DebugEvaluateCondition $ do
        let predicates = [predicate1, predicate2]
        predicate <- predicates
        sideConditions <- inits predicates
        [DebugEvaluateCondition (predicate :| sideConditions)]

predicate1, predicate2 :: Predicate VariableName
predicate1 = makeEqualsPredicate (Mock.f Mock.a) (Mock.g Mock.b)
predicate2 = makeEqualsPredicate (Mock.g Mock.a) (Mock.h Mock.c)
