module Test.Kore.Step.Simplification.InjSimplifier
    ( test_unifyInj
    , test_normalize
    ) where

import Prelude.Kore

import Test.Tasty

import Kore.Internal.Inj
import Kore.Internal.TermLike hiding
    ( Top (..)
    )
import Kore.Rewriting.RewritingVariable
    ( RewritingVariableName
    , mkElementConfigVariable
    )
import Kore.Step.Simplification.InjSimplifier
import Pair

import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
import Test.Kore.Step.MockSymbols
import Test.Tasty.HUnit.Ext

mkInj :: Sort -> TermLike RewritingVariableName -> TermLike RewritingVariableName
mkInj = sortInjection

inj
    :: Sort
    -> TermLike RewritingVariableName
    -> Inj (TermLike RewritingVariableName)
inj injTo injChild = inj' (termLikeSort injChild) injTo injChild

inj' :: Sort -> Sort -> child -> Inj child
inj' injFrom injTo injChild =
    Inj
        { injConstructor = sortInjectionId
        , injFrom
        , injTo
        , injChild
        , injAttributes = Mock.sortInjectionAttributes
        }

{- Sorts

    + Top
    |
    >---+ Test
    |   |
    |   >---+ 0
    |   |
    >--->---+ Sub
    |       |
    >--->--->---+ SubSub
    |   |
    >---+ Other

 -}

ctorSub, ctorSubSub, ctorOther, ctorTest1, ctorTest2
    :: TermLike RewritingVariableName
ctorSub = aSubsort
ctorSubSub = aSubSubsort
ctorOther = aOtherSort
ctorTest1 = cf
ctorTest2 = cg

simplSub, simplOther, simpl0 :: TermLike RewritingVariableName
simplSub = plain00Subsort
simplOther = plain00OtherSort
simpl0 = plain00Sort0

xSub :: TermLike RewritingVariableName
xSub = mkElemVar (mkElementVariable "xSub" subSort & mkElementConfigVariable)

test_unifyInj :: [TestTree]
test_unifyInj =
    [ test "inj{Test, Top}(ctorTest1) ∧ inj{Test, Top}(ctorTest2)"
        {-
            Injections with the same child sort are unifiable.
         -}
        (inj topSort ctorTest1)
        (inj topSort ctorTest2)
        (Right (inj' testSort topSort (Pair ctorTest1 ctorTest2)))
    , test "inj{SubSub, Top}(ctorSubSub) ∧ inj{Sub, Top}(x:Sub)"
        {-
            Injections with
                - different child sorts, and
                - the first sort is a subsort of the second
            are unifiable.
         -}
        (inj topSort ctorSubSub)
        (inj topSort xSub)
        (Right (inj' subSort topSort (Pair (mkInj subSort ctorSubSub) xSub)))
    , test "inj{Sub, Top}(x:Sub) ∧ inj{SubSub, Top}(ctorSubSub)"
        {-
            Injections with
                - different child sorts, and
                - the second sort is a subsort of the first
            are unifiable.
         -}
        (inj topSort xSub)
        (inj topSort ctorSubSub)
        (Right (inj' subSort topSort (Pair xSub (mkInj subSort ctorSubSub))))
    , test "inj{Test, Top}(ctorTest1) ∧ inj{Other, Top}(ctorOther)"
        {-
            Injections with
                - different child sorts, and
                - neither sort is a subsort of the other
            are known to be distinct.
         -}
        (inj topSort ctorTest1)
        (inj topSort ctorOther)
        (Left Distinct)
    , test "inj{Sub, Top}(simplSub) ∧ inj{Other, Top}(simplOther)"
        {-
            Injections with
                - different child sorts, and
                - a common subsort, and
                - simplifiable children
            are not known to be distinct.
         -}
        (inj topSort simplSub)
        (inj topSort simplOther)
        (Left Unknown)
    , test "inj{Sub, Top}(ctorSub) ∧ inj{Other, Top}(simplOther)"
        {-
            Injections with
                - different child sorts, and
                - a common subsort, and
                - at least one constructor-like child
            are known to be distinct.
         -}
        (inj topSort ctorSub)
        (inj topSort simplOther)
        (Left Distinct)
    , test "inj{0, Top}(simpl0) ∧ inj{Other, Top}(simplOther)"
        {-
            Injections with
                - different child sorts, and
                - no common subsorts
            are known to be distinct.
         -}
        (inj topSort simpl0)
        (inj topSort simplOther)
        (Left Distinct)
    ]
  where
    test
        :: HasCallStack
        => TestName
        -> Inj (TermLike RewritingVariableName)
        -> Inj (TermLike RewritingVariableName)
        -> Either Distinct (Inj (Pair (TermLike RewritingVariableName)))
        -> TestTree
    test testName inj1 inj2 expect =
        testCase testName (assertEqual "" expect (unifyInj inj1 inj2))
    InjSimplifier { unifyInj } = injSimplifier

test_normalize :: [TestTree]
test_normalize =
    [ test "nested sort injection"
        (mkInj topSort (mkInj testSort (mkInj subSort ctorSubSub)))
        (mkInj topSort ctorSubSub)
    ]
  where
    test
        :: HasCallStack
        => TestName
        -> TermLike RewritingVariableName
        -> TermLike RewritingVariableName
        -> TestTree
    test testName original expect =
        let actual = normalize injSimplifier original
        in testCase testName (assertEqual "" expect actual)
