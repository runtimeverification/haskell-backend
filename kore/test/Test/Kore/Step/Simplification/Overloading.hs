module Test.Kore.Step.Simplification.Overloading
    ( test_matchOverloading
    , test_unifyOverloading
    ) where

import Prelude.Kore

import Test.Tasty

import Control.Monad.Trans.Except
    ( runExceptT
    )
import Data.Text
    ( Text
    )

import qualified Kore.Builtin.Bool.Bool as Bool
import qualified Kore.Builtin.Int.Int as Int
import qualified Kore.Builtin.String.String as String
import Kore.Internal.Predicate
import Kore.Internal.TermLike
import Kore.Step.Simplification.Overloading
import Pair
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Ext

test_matchOverloading :: [TestTree]
test_matchOverloading =
    [ testGroup "Matching overloads"
        [ matches "direct overload, left side"
            ( Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort)
            , Mock.sortInjectionOtherToTop (Mock.otherOverload Mock.aOtherSort)
            )
            ( Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort)
            , Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort)
            )
        , matches "direct overload, right side"
            ( Mock.sortInjectionOtherToTop (Mock.otherOverload Mock.aOtherSort)
            , Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort)
            )
            ( Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort)
            , Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort)
            )
        , matches "overload, both sides, unifiable"
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
        , matches "overload, both sides, unifiable, with injection"
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
        , doesn'tMatch "overload, both sides, not unifiable"
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
        , doesn'tMatch "overload vs injected constructor"
            (Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort))
            (Mock.sortInjectionOtherToTop Mock.aOtherSort)
            "different injected ctor"
        , doesn'tMatch "overload vs injected domain value"
            (Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort))
            (Mock.sortInjectionOtherToTop otherDomainValue)
            "injected domain value"
        , doesn'tMatch "injected domain value vs overload"
            (Mock.sortInjectionOtherToTop otherDomainValue)
            (Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort))
            "injected domain value"
        , doesn'tMatch "overload vs injected int"
            (Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort))
            (Mock.sortInjectionOtherToTop (Int.asInternal Mock.otherSort 0))
            "injected builtin int"
        , doesn'tMatch "overload vs injected bool"
            (Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort))
            (Mock.sortInjectionOtherToTop (Bool.asInternal Mock.otherSort True))
            "injected builtin bool"
        , doesn'tMatch "overload vs injected string"
            (Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort))
            (Mock.sortInjectionOtherToTop (String.asInternal Mock.otherSort ""))
            "injected builtin string"
        , matchNotApplicable "direct overload vs. variable, left side"
            (Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort))
            (Mock.sortInjectionOtherToTop (mkElemVar Mock.xOtherSort))
        , matchNotApplicable "overload vs injected non-constructor"
            (Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort))
            (Mock.sortInjectionOtherToTop Mock.plain00OtherSort)
        , matchNotApplicable "overload vs injected top"
            (Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort))
            (Mock.sortInjectionOtherToTop (mkTop Mock.otherSort))
        , matchNotApplicable "unrelated"
            Mock.aOtherSort
            Mock.plain00OtherSort
        , matchNotApplicableTwice "direct overload, left side"
            (Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort))
            (Mock.sortInjectionOtherToTop (Mock.otherOverload Mock.aOtherSort))
        , matchNotApplicableTwice "direct overload, right side"
            (Mock.sortInjectionOtherToTop (Mock.otherOverload Mock.aOtherSort))
            (Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort))
        , matchNotApplicableTwice "overload, both sides, unifiable"
            (Mock.sortInjectionOtherToTop
               (Mock.otherOverload
                   (Mock.sortInjectionSubSubToOther Mock.aSubSubsort)
               )
            )
            (Mock.sortInjectionSubToTop
               (Mock.subOverload
                   (Mock.sortInjectionSubSubToSub Mock.aSubSubsort)
               )
            )
        , matchNotApplicableTwice
            "overload, both sides, unifiable, with injection"
            (Mock.sortInjectionOtherToOverTheTop
               (Mock.otherOverload
                   (Mock.sortInjectionSubSubToOther Mock.aSubSubsort)
               )
            )
            (Mock.sortInjectionSubToOverTheTop
               (Mock.subOverload
                   (Mock.sortInjectionSubSubToSub Mock.aSubSubsort)
               )
            )
         ]
    ]

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
        , narrows "direct overload vs. variable, left side; var direct"
            ( Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort)
            , Mock.sortInjectionSubToTop (mkElemVar Mock.xSubSort)
            )
            ( ( Mock.xSubSort
              , Mock.subOverload x1
              )
            , ( Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort)
              , Mock.topOverload (Mock.sortInjectionSubToTop x1)
              )
            )
        , narrows "direct overload vs. variable, left side; var inject"
            ( Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort)
            , Mock.sortInjectionTestToTop (mkElemVar Mock.x)
            )
            ( ( Mock.x
              , Mock.sortInjectionSubToTest (Mock.subOverload x1)
              )
            , ( Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort)
              , Mock.topOverload (Mock.sortInjectionSubToTop x1)
              )
            )
        , narrows "injected overload vs injected variable, unifiable"
            ( Mock.sortInjectionOtherToTop
               (Mock.otherOverload
                   (Mock.sortInjectionSubSubToOther Mock.aSubSubsort)
               )
            , Mock.sortInjectionTestToTop (mkElemVar Mock.x)
            )
            ( ( Mock.x
              , Mock.sortInjectionSubToTest (Mock.subOverload x1)
              )
            , ( Mock.topOverload
                (Mock.sortInjectionSubSubToTop Mock.aSubSubsort)
              , Mock.topOverload (Mock.sortInjectionSubToTop x1)
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
        , doesn'tUnify "injected overload vs injected variable"
            ( Mock.sortInjectionSubSubToTop
               (Mock.subsubOverload Mock.aSubSubsort)
            )
            (Mock.sortInjectionSubOtherToTop (mkElemVar Mock.xSubOtherSort))
            "overloaded constructors not unifiable"
        , unifyNotApplicable "overload vs injected non-constructor"
            (Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort))
            (Mock.sortInjectionOtherToTop Mock.plain00OtherSort)
        , unifyNotApplicable "overload vs injected top"
            (Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort))
            (Mock.sortInjectionOtherToTop (mkTop Mock.otherSort))
        , unifyNotApplicable "unrelated"
            Mock.aOtherSort
            Mock.plain00OtherSort
        , unifyNotApplicableTwice "direct overload, left side"
            (Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort))
            (Mock.sortInjectionOtherToTop (Mock.otherOverload Mock.aOtherSort))
        , unifyNotApplicableTwice "direct overload, right side"
            (Mock.sortInjectionOtherToTop (Mock.otherOverload Mock.aOtherSort))
            (Mock.topOverload (Mock.sortInjectionOtherToTop Mock.aOtherSort))
        , unifyNotApplicableTwice "overload, both sides, unifiable"
            (Mock.sortInjectionOtherToTop
               (Mock.otherOverload
                   (Mock.sortInjectionSubSubToOther Mock.aSubSubsort)
               )
            )
            (Mock.sortInjectionSubToTop
               (Mock.subOverload
                   (Mock.sortInjectionSubSubToSub Mock.aSubSubsort)
               )
            )
        , unifyNotApplicableTwice
            "overload, both sides, unifiable, with injection"
            (Mock.sortInjectionOtherToOverTheTop
               (Mock.otherOverload
                   (Mock.sortInjectionSubSubToOther Mock.aSubSubsort)
               )
            )
            (Mock.sortInjectionSubToOverTheTop
               (Mock.subOverload
                   (Mock.sortInjectionSubSubToSub Mock.aSubSubsort)
               )
            )
         ]
    ]

otherDomainValue :: TermLike Variable
otherDomainValue =
    mkDomainValue DomainValue
        { domainValueSort = Mock.otherSort
        , domainValueChild = mkStringLiteral "a"
        }

matches
    :: HasCallStack
    => TestName
    -> (TermLike Variable, TermLike Variable)
    -> (TermLike Variable, TermLike Variable)
    -> TestTree
matches comment (term1, term2) (term1', term2') =
    withMatching
        (assertEqual "" (Right (Pair term1' term2')))
        comment
        (Pair term1 term2)

doesn'tMatch
    :: HasCallStack
    => TestName
    -> TermLike Variable
    -> TermLike Variable
    -> String
    -> TestTree
doesn'tMatch comment term1 term2 reason
    = withMatching
        (assertEqual "" (Left (Clash reason)))
        comment
        (Pair term1 term2)

matchNotApplicable
    :: HasCallStack
    => TestName
    -> TermLike Variable
    -> TermLike Variable
    -> TestTree
matchNotApplicable comment term1 term2
    = withMatching
        (assertEqual "" (Left NotApplicable))
        comment
        (Pair term1 term2)

matchNotApplicableTwice
    :: HasCallStack
    => TestName
    -> TermLike Variable
    -> TermLike Variable
    -> TestTree
matchNotApplicableTwice comment term1 term2
    = withMatchingTwice
        (assertEqual "" (Left NotApplicable))
        comment
        (Pair term1 term2)

unifies
    :: HasCallStack
    => TestName
    -> (TermLike Variable, TermLike Variable)
    -> (TermLike Variable, TermLike Variable)
    -> TestTree
unifies comment (term1, term2) (term1', term2') =
    withUnification
        (assertEqual "" (Right (Simple (Pair term1' term2'))))
        comment
        (Pair term1 term2)

narrows
    :: HasCallStack
    => TestName
    -> (TermLike Variable, TermLike Variable)
    ->  ( (ElementVariable Variable, TermLike Variable)
        , (TermLike Variable, TermLike Variable)
        )
    -> TestTree
narrows comment (term1, term2) ((v, term), (term1', term2')) =
    withUnification
        checkNarrowing
        comment
        (Pair term1 term2)
  where
    checkNarrowing :: UnificationResult -> Assertion
    checkNarrowing
        (Right (WithNarrowing
            Narrowing { narrowedSubst, narrowedPair}
        ))
      = do
        assertEqual "" (Pair term1' term2') narrowedPair
        assertEqual "" (makeEqualsPredicate_ (mkElemVar v) term) narrowedSubst
    checkNarrowing _ = assertFailure "Expected narrowing solution"


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

unifyNotApplicable
    :: HasCallStack
    => TestName
    -> TermLike Variable
    -> TermLike Variable
    -> TestTree
unifyNotApplicable comment term1 term2
    = withUnification
        (assertEqual "" (Left NotApplicable))
        comment
        (Pair term1 term2)

unifyNotApplicableTwice
    :: HasCallStack
    => TestName
    -> TermLike Variable
    -> TermLike Variable
    -> TestTree
unifyNotApplicableTwice comment term1 term2
    = withUnificationTwice
        (assertEqual "" (Left NotApplicable))
        comment
        (Pair term1 term2)

type MatchResult = Either UnifyOverloadingError (Pair (TermLike Variable))

match
    :: Pair (TermLike Variable)
    -> IO MatchResult
match termPair = runSimplifier Mock.env $ runExceptT matchResult
  where
    matchResult :: MatchOverloadingResult Simplifier Variable
    matchResult = matchOverloading termPair

withMatching
    :: (MatchResult -> Assertion)
    -> TestName
    -> Pair (TermLike Variable)
    -> TestTree
withMatching check comment termPair =
    testCase comment $ do
        actual <- match termPair
        check actual

withMatchingTwice
    :: (MatchResult -> Assertion)
    -> TestName
    -> Pair (TermLike Variable)
    -> TestTree
withMatchingTwice check comment termPair =
    testCase comment $ do
        actual <- match termPair
        case actual of
            Left _ -> assertFailure "Expected matching solution."
            Right termPair' -> do
                actual' <- match termPair'
                check actual'

type UnificationResult =
    Either UnifyOverloadingError (OverloadingResolution Variable)

unify
    :: Pair (TermLike Variable)
    -> IO UnificationResult
unify termPair = runSimplifier Mock.env $ runExceptT unifyResult
  where
    unifyResult :: UnifyOverloadingResult Simplifier Variable
    unifyResult = unifyOverloading termPair

withUnification
    :: (UnificationResult -> Assertion)
    -> TestName
    -> Pair (TermLike Variable)
    -> TestTree
withUnification check comment termPair =
    testCase comment $ do
        actual <- unify termPair
        check actual

withUnificationTwice
    :: (UnificationResult -> Assertion)
    -> TestName
    -> Pair (TermLike Variable)
    -> TestTree
withUnificationTwice check comment termPair =
    testCase comment $ do
        actual <- unify termPair
        case actual of
            Left _ -> assertFailure "Expected matching solution."
            Right (Simple termPair') -> do
                actual' <- unify termPair'
                check actual'
            Right (WithNarrowing Narrowing { narrowedPair }) -> do
                actual' <- unify narrowedPair
                check actual'

x1 :: TermLike Variable
x1 = mkElemVar $ ElementVariable
    $ Variable (generatedId "x1") mempty Mock.subSort

generatedId :: Text -> Id
generatedId name =
    Id
        { getId = name
        , idLocation = AstLocationGeneratedVariable
        }

