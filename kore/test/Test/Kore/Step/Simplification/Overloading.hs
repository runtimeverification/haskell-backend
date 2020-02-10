module Test.Kore.Step.Simplification.Overloading
    ( test_unifyOverloading
    ) where

import Prelude.Kore

import Test.Tasty

import Control.Monad.Trans.Except
    ( runExceptT
    )

import qualified Kore.Builtin.Bool.Bool as Bool
import qualified Kore.Builtin.Int.Int as Int
import qualified Kore.Builtin.String.String as String
import Kore.Internal.TermLike
import Kore.Step.Simplification.Overloading
import Pair
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext

test_unifyOverloading :: [TestTree]
test_unifyOverloading =
    [ testGroup "Unifying overloads"
        [ unifies "direct overload, left side"
            ( Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort)
            , Mock.sortInjectionOtherToTop (Mock.otherOverload Mock.aOtherSort)
            )
            ( Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort)
            , Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort)
            )
        , unifies "direct overload, right side"
            ( Mock.sortInjectionOtherToTop (Mock.otherOverload Mock.aOtherSort)
            , Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort)
            )
            ( Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort)
            , Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort)
            )
        , unifies "overload, both sides, unifiable"
            ( Mock.sortInjectionOtherToTop
               (Mock.otherOverload
                   (Mock.sortInjectionSubSubToOther Mock.aSubSubsort)
               )
            , Mock.sortInjectionSubToTop
               (Mock.subOverload
                   (Mock.sortInjectionSubSubToSub Mock.aSubSubsort)
               )
            )
            ( Mock.topOverload (Mock.sortInjectionSubSubToTop Mock.aSubSubsort)
            , Mock.topOverload (Mock.sortInjectionSubSubToTop Mock.aSubSubsort)
            )
        , unifies "overload, both sides, unifiable, with injection"
            ( Mock.sortInjectionOtherToOverTheTop
               (Mock.otherOverload
                   (Mock.sortInjectionSubSubToOther Mock.aSubSubsort)
               )
            , Mock.sortInjectionSubToOverTheTop
               (Mock.subOverload
                   (Mock.sortInjectionSubSubToSub Mock.aSubSubsort)
               )
            )
            ( Mock.sortInjectionTopToOverTheTop
                (Mock.topOverload
                    (Mock.sortInjectionSubSubToTop Mock.aSubSubsort)
                )
            , Mock.sortInjectionTopToOverTheTop
                (Mock.topOverload
                    (Mock.sortInjectionSubSubToTop Mock.aSubSubsort)
                )
            )
        , doesn'tUnify "overload, both sides, not unifiable"
            (Mock.sortInjectionOtherToOtherTop
                 (Mock.otherOverload
                     (Mock.sortInjectionSubSubToOther Mock.aSubSubsort)
                 )
            )
            (Mock.sortInjectionSubToOtherTop
                 (Mock.subOverload
                     (Mock.sortInjectionSubSubToSub Mock.aSubSubsort)
                 )
            )
            "overloaded constructors not unifiable"
        , doesn'tUnify "overload vs injected constructor"
            (Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort))
            (Mock.sortInjectionOtherToTop Mock.aOtherSort)
            "different injected ctor"
        , doesn'tUnify "overload vs injected domain value"
            (Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort))
            (Mock.sortInjectionOtherToTop otherDomainValue)
            "injected domain value"
        , doesn'tUnify "injected domain value vs overload"
            (Mock.sortInjectionOtherToTop otherDomainValue)
            (Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort))
            "injected domain value"
        , doesn'tUnify "overload vs injected int"
            (Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort))
            (Mock.sortInjectionOtherToTop (Int.asInternal Mock.otherSort 0))
            "injected builtin int"
        , doesn'tUnify "overload vs injected bool"
            (Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort))
            (Mock.sortInjectionOtherToTop (Bool.asInternal Mock.otherSort True))
            "injected builtin bool"
        , doesn'tUnify "overload vs injected string"
            (Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort))
            (Mock.sortInjectionOtherToTop (String.asInternal Mock.otherSort ""))
            "injected builtin string"
        , notApplicable "overload vs injected non-constructor"
            (Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort))
            (Mock.sortInjectionOtherToTop Mock.plain00OtherSort)
        , notApplicable "overload vs injected top"
            (Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort))
            (Mock.sortInjectionOtherToTop (mkTop Mock.otherSort))
        , notApplicable "unrelated"
            Mock.aOtherSort
            Mock.plain00OtherSort
        ]
    ]

otherDomainValue :: TermLike Variable
otherDomainValue =
    mkDomainValue DomainValue
        { domainValueSort = Mock.otherSort
        , domainValueChild = mkStringLiteral "a"
        }

unifies
    :: HasCallStack
    => TestName
    -> (TermLike Variable, TermLike Variable)
    -> (TermLike Variable, TermLike Variable)
    -> TestTree
unifies comment (term1, term2) (term1', term2') =
    withUnification
        (assertEqual "" (Right (Pair term1' term2')))
        comment
        (Pair term1 term2)

doesn'tUnify
    :: HasCallStack
    => TestName
    -> TermLike Variable
    -> TermLike Variable
    -> String
    -> TestTree
doesn'tUnify comment term1 term2 reason
    = withUnification
        (assertEqual "" (Left (Clash reason)))
        comment
        (Pair term1 term2)

notApplicable
    :: HasCallStack
    => TestName
    -> TermLike Variable
    -> TermLike Variable
    -> TestTree
notApplicable comment term1 term2
    = withUnification
        (assertEqual "" (Left NotApplicable))
        comment
        (Pair term1 term2)

type UnifyResult = Either UnifyOverloadingError (Pair (TermLike Variable))

unify
    :: Pair (TermLike Variable)
    -> IO UnifyResult
unify termPair = runSimplifier Mock.env $ runExceptT unifyResult
  where
    unifyResult :: UnifyOverloading Simplifier (TermLike Variable)
    unifyResult = unifyOverloading termPair

withUnification
    :: (UnifyResult -> Assertion)
    -> TestName
    -> Pair (TermLike Variable)
    -> TestTree
withUnification check comment termPair =
    testCase comment $ do
        actual <- unify termPair
        check actual
