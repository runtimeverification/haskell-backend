module Test.Kore.Simplify.InternalList (
    test_simplify,
) where

import qualified Data.Sequence as Seq
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.InternalList
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    makeCeilPredicate,
 )
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.InternalList (
    simplify,
 )
import Prelude.Kore
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_simplify :: [TestTree]
test_simplify =
    [ becomes "\\bottom element" (mkList [bottom]) []
    , becomes
        "distributes \\or - 1"
        (mkList [a <> b])
        [ mkList [Mock.a] & mkInternalList & Pattern.fromTermLike
        , mkList [Mock.b] & mkInternalList & Pattern.fromTermLike
        ]
    , becomes
        "distributes \\or - 2"
        (mkList [a <> b, a <> b])
        [ mkList [Mock.a, Mock.a] & mkInternalList & Pattern.fromTermLike
        , mkList [Mock.a, Mock.b] & mkInternalList & Pattern.fromTermLike
        , mkList [Mock.b, Mock.b] & mkInternalList & Pattern.fromTermLike
        , mkList [Mock.b, Mock.a] & mkInternalList & Pattern.fromTermLike
        ]
    , becomes
        "collects \\and"
        ( mkList
            [ Pattern.withCondition Mock.a ceila
            , Pattern.withCondition Mock.b ceilb
            ]
            & fmap OrPattern.fromPattern
        )
        [ Pattern.withCondition
            (mkList [Mock.a, Mock.b] & mkInternalList)
            (ceila <> ceilb)
        ]
    ]
  where
    a = OrPattern.fromTermLike Mock.a
    b = OrPattern.fromTermLike Mock.b
    ceila =
        makeCeilPredicate (Mock.f Mock.a)
            & Condition.fromPredicate
    ceilb =
        makeCeilPredicate (Mock.f Mock.b)
            & Condition.fromPredicate
    bottom = OrPattern.fromPatterns [Pattern.bottom]
    becomes ::
        HasCallStack =>
        TestName ->
        InternalList (OrPattern RewritingVariableName) ->
        [Pattern RewritingVariableName] ->
        TestTree
    becomes name origin expect =
        testCase name $
            assertEqual
                ""
                (OrPattern.fromPatterns expect)
                (evaluate origin)

mkList :: [child] -> InternalList child
mkList children =
    InternalList
        { internalListSort = Mock.listSort
        , internalListUnit = Mock.unitListSymbol
        , internalListElement = Mock.elementListSymbol
        , internalListConcat = Mock.concatListSymbol
        , internalListChild = Seq.fromList children
        }

evaluate :: InternalList (OrPattern RewritingVariableName) -> OrPattern RewritingVariableName
evaluate = simplify
