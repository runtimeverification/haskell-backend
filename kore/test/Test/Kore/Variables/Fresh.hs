{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Test.Kore.Variables.Fresh
    ( test_refreshVariable
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import Data.Maybe
    ( fromJust
    , isJust
    )
import Data.Set
    ( Set
    )
import qualified Data.Set as Set

import Kore.Sort
import Kore.Syntax.ElementVariable
    ( ElementVariable (..)
    )
import Kore.Syntax.SetVariable
    ( SetVariable (..)
    )
import Kore.Variables.Fresh
import Kore.Variables.Target
    ( Target (..)
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import Test.Kore

metaVariable :: Variable
metaVariable = Variable
    { variableName = testId "#v"
    , variableCounter = mempty
    , variableSort = SortVariableSort (SortVariable (testId "#s"))
    }

metaVariableDifferentSort :: Variable
metaVariableDifferentSort = Variable
    { variableName = testId "#v"
    , variableCounter = mempty
    , variableSort = SortVariableSort (SortVariable (testId "#s1"))
    }

test_refreshVariable :: [TestTree]
test_refreshVariable =
    [ testCase "refreshVariable - avoid empty set" $
        assertEqual "Expected no new variable"
            Nothing
            (refreshVariable Set.empty original)

    , testCase "refreshVariable - avoid original" $
        assertBool "Expected fresh variable" (original < fresh0 original)

    , testCase "refreshVariable - avoid fresh" $
        assertBool "Expected another fresh variable" (fresh0 original < fresh1 original)

    , testCase "refreshVariable - expecting the same sort" $
        assertBool "Expected fresh variable has same sort as original"
            (variableSort original == variableSort fresh2)

    , testCase "refreshVariable - sort order does not matter" $
        let assertRefreshes a b =
                assertBool "Expected fresh variable"
                    (isJust (refreshVariable (Set.singleton a) b))
        in do
            assertRefreshes original metaVariableDifferentSort
            assertRefreshes metaVariableDifferentSort original

    -- ElementVariable Variable
    , testCase "refreshVariable - avoid empty set" $
        assertEqual "Expected no new variable"
            Nothing
            (refreshVariable Set.empty elemOriginal)

    , testCase "refreshVariable - avoid original" $
        assertBool "Expected fresh variable" (elemOriginal < fresh0 elemOriginal)

    , testCase "refreshVariable - avoid fresh" $
        assertBool "Expected another fresh variable" (fresh0 elemOriginal < fresh1 elemOriginal)

    -- SetVariable Variable
    , testCase "refreshVariable - avoid empty set" $
        assertEqual "Expected no new variable"
            Nothing
            (refreshVariable Set.empty setOriginal)

    , testCase "refreshVariable - avoid original" $
        assertBool "Expected fresh variable" (setOriginal < fresh0 setOriginal)

    , testCase "refreshVariable - avoid fresh" $
        assertBool "Expected another fresh variable" (fresh0 setOriginal < fresh1 setOriginal)

    -- UnifiedVariable (ElementVariable Variable)
    , testCase "refreshVariable - avoid empty set" $
        assertEqual "Expected no new variable"
            Nothing
            (refreshVariable Set.empty elemOriginal)

    , testCase "refreshVariable - avoid original" $
        assertBool "Expected fresh variable" (unifiedElemOriginal < fresh0 unifiedElemOriginal)

    , testCase "refreshVariable - avoid fresh" $
        assertBool "Expected another fresh variable" (fresh0 unifiedElemOriginal < fresh1 unifiedElemOriginal)

    -- UnifiedVariable (SetVariable Variable)
    , testCase "refreshVariable - avoid empty set" $
        assertEqual "Expected no new variable"
            Nothing
            (refreshVariable Set.empty unifiedSetOriginal)

    , testCase "refreshVariable - avoid original" $
        assertBool "Expected fresh variable" (unifiedSetOriginal < fresh0 unifiedSetOriginal)

    , testCase "refreshVariable - avoid fresh" $
        assertBool "Expected another fresh variable" (fresh0 unifiedSetOriginal < fresh1 unifiedSetOriginal)

    -- ElementVariable (Target Variable)
    , testCase "refreshVariable - avoid empty set" $
        assertEqual "Expected no new variable"
            Nothing
            (refreshVariable Set.empty elemTargetOriginal)

    , testCase "refreshVariable - avoid original" $
        assertBool "Expected fresh variable" (elemTargetOriginal < fresh0 elemTargetOriginal)

    , testCase "refreshVariable - avoid original (ignore Target constructor)" $
        assertBool "Expected fresh variable" (elemTargetOriginal < fresh avoidET elemTargetOriginal)

    , testCase "refreshVariable - avoid fresh" $
        assertBool "Expected another fresh variable" (fresh0 elemTargetOriginal < fresh1 elemTargetOriginal)

    -- SetVariable (Target Variable)
    , testCase "refreshVariable - avoid empty set" $
        assertEqual "Expected no new variable"
            Nothing
            (refreshVariable Set.empty setNonTargetOriginal)

    , testCase "refreshVariable - avoid original" $
        assertBool "Expected fresh variable" (setNonTargetOriginal < fresh0 setNonTargetOriginal)

    , testCase "refreshVariable - avoid original (ignore Target constructor)" $
        assertBool "Expected fresh variable" (setNonTargetOriginal < fresh avoidST setNonTargetOriginal)

    , testCase "refreshVariable - avoid fresh" $
        assertBool "Expected another fresh variable" (fresh0 setNonTargetOriginal < fresh1 setNonTargetOriginal)

    -- UnifiedVariable (Target Variable)
    , testCase "refreshVariable - avoid empty set" $
        assertEqual "Expected no new variable"
            Nothing
            (refreshVariable Set.empty unifiedElemTargetOriginal)

    , testCase "refreshVariable - avoid original" $
        assertBool "Expected fresh variable" (unifiedElemTargetOriginal < fresh0 unifiedElemTargetOriginal)

    , testCase "refreshVariable - avoid original (ignore Target constructor)" $
        assertBool "Expected fresh variable" (unifiedElemTargetOriginal < fresh avoidUET unifiedElemTargetOriginal)

    , testCase "refreshVariable - avoid fresh" $
        assertBool "Expected another fresh variable" (fresh0 unifiedElemTargetOriginal < fresh1 unifiedElemTargetOriginal)
    , testCase "refreshVariable - avoid empty set" $
        assertEqual "Expected no new variable"
            Nothing
            (refreshVariable Set.empty unifiedSetNonTargetOriginal)

    , testCase "refreshVariable - avoid original" $
        assertBool "Expected fresh variable" (unifiedSetNonTargetOriginal < fresh0 unifiedSetNonTargetOriginal)

    , testCase "refreshVariable - avoid original (ignore Target constructor)" $
        assertBool "Expected fresh variable" (unifiedSetNonTargetOriginal < fresh avoidUST unifiedSetNonTargetOriginal)

    , testCase "refreshVariable - avoid fresh" $
        assertBool "Expected another fresh variable" (fresh0 unifiedSetNonTargetOriginal < fresh1 unifiedSetNonTargetOriginal)
    ]
  where
    original = metaVariable
    avoid2 = Set.singleton metaVariableDifferentSort
    Just fresh2 = refreshVariable avoid2 original

    avoid0 :: variable -> Set variable
    avoid0 var = Set.singleton var

    avoid1 :: FreshVariable variable => variable -> Set variable
    avoid1 var = Set.insert (fresh0 var) (avoid0 var)

    fresh0, fresh1 :: FreshVariable variable => variable -> variable
    fresh0 var = fromJust $ refreshVariable (avoid0 var) var
    fresh1 var = fromJust $ refreshVariable (avoid1 var) var
    fresh :: FreshVariable variable => Set variable -> variable -> variable
    fresh avoiding var = fromJust $ refreshVariable avoiding var

    elemOriginal        = ElementVariable original
    setOriginal         = SetVariable original
    unifiedElemOriginal = ElemVar elemOriginal
    unifiedSetOriginal  = SetVar setOriginal

    -- ElementVariable (Target Variable)
    elemTargetOriginal    = Target <$> elemOriginal
    elemNonTargetOriginal = NonTarget <$> elemOriginal
    avoidET = Set.singleton elemNonTargetOriginal
    -- SetVariable (Target Variable)
    setTargetOriginal     = Target <$> setOriginal
    setNonTargetOriginal  = NonTarget <$> setOriginal
    avoidST = Set.singleton setTargetOriginal

    -- UnifiedVariable (Target Variable)
    unifiedElemTargetOriginal    = Target <$> unifiedElemOriginal
    unifiedElemNonTargetOriginal = NonTarget <$> unifiedElemOriginal
    unifiedSetTargetOriginal     = Target <$> unifiedSetOriginal
    unifiedSetNonTargetOriginal  = NonTarget <$> unifiedSetOriginal
    avoidUET = Set.singleton unifiedElemNonTargetOriginal
    avoidUST = Set.singleton unifiedSetTargetOriginal
