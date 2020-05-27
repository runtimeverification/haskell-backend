{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Test.Kore.Variables.Fresh
    ( test_refreshVariable
    , test_FreshPartialOrd_Variable
    , test_FreshPartialOrd_ElementVariable
    , test_FreshPartialOrd_SetVariable
    , test_FreshPartialOrd_UnifiedVariable
    , test_FreshPartialOrd_VariableName
    , test_FreshPartialOrd_ElementVariableName
    , test_FreshPartialOrd_SetVariableName
    , test_FreshPartialOrd_SomeVariableName
    --
    , testFreshPartialOrd
    , relatedVariableGen
    , relatedUnifiedVariableGen
    , relatedVariableNameGen
    , someVariableNameGen
    ) where

import Prelude.Kore

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Test.Tasty
import Test.Tasty.Hedgehog
import Test.Tasty.HUnit

import Data.Maybe
    ( fromJust
    )
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import Numeric.Natural

import Data.Sup
import Kore.Sort
import Kore.Syntax.ElementVariable
    ( ElementVariable (..)
    )
import Kore.Syntax.SetVariable
    ( SetVariable (..)
    )
import Kore.Variables.Fresh
import Kore.Variables.Target
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    , mapUnifiedVariable
    )
import Pair

import Test.Kore
    ( idGen
    , testId
    )
import Test.Kore.Step.MockSymbols
    ( subSort
    , testSort
    , testSort0
    , testSort1
    , topSort
    )

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
    [ testCase "same name, different sort" $ do
        let x0 = Variable (testId "x0") Nothing testSort0
            x1 = x0 { variableSort = testSort1 }
            x1' = x1 { variableCounter = Just (Element 0) }
        let avoiding = Set.singleton x0
        assertEqual "Expected fresh variable"
            (Just x1')
            (refreshVariable avoiding x1)

    , testGroup "instance FreshVariable Variable"
        [ testCase "refreshVariable - avoid empty set" $
            assertEqual "Expected no new variable"
                Nothing
                (refreshVariable Set.empty original)

        , testCase "refreshVariable - avoid original" $
            assertBool "Expected fresh variable" (original < fresh0 original)

        , testCase "refreshVariable - avoid fresh" $
            assertBool
                "Expected another fresh variable"
                (fresh0 original < fresh1 original)

        , testCase "refreshVariable - expecting the same sort" $
            assertBool
                "Expected fresh variable has same sort as original"
                (variableSort original == variableSort fresh2)

        , testCase "refreshVariable - sort order does not matter" $
            let assertRefreshes a b =
                    assertBool "Expected fresh variable"
                        (isJust (refreshVariable (Set.singleton a) b))
            in do
                assertRefreshes original metaVariableDifferentSort
                assertRefreshes metaVariableDifferentSort original
        ]

    , testGroup "instance FreshVariable (Target Variable)"
        [ testCase "refreshVariable - avoid empty set" $
            assertEqual "Expected no new variable"
                Nothing
                (refreshVariable Set.empty targetOriginal)

        , testCase "refreshVariable - avoid original" $
            assertBool
                "Expected fresh variable"
                (targetOriginal < fresh0 targetOriginal)

        , testCase "refreshVariable - avoid original (ignore Target constructor)" $
            assertBool
                "Expected fresh variable"
                (targetOriginal < fresh avoidT targetOriginal)

        , testCase "refreshVariable - avoid fresh" $
            assertBool
                "Expected another fresh variable"
                (fresh0 targetOriginal < fresh1 targetOriginal)
        ]

    , testGroup "instance FreshVariable (ElementVariable Variable)"
        [ testCase "refreshVariable - avoid empty set" $
            assertEqual "Expected no new variable"
                Nothing
                (refreshVariable Set.empty elemOriginal)

        , testCase "refreshVariable - avoid original" $
            assertBool
                "Expected fresh variable"
                (elemOriginal < fresh0 elemOriginal)

        , testCase "refreshVariable - avoid fresh" $
            assertBool
                "Expected another fresh variable"
                (fresh0 elemOriginal < fresh1 elemOriginal)
        ]

    , testGroup "instance FreshVariable (SetVariable Variable)"
        [ testCase "refreshVariable - avoid empty set" $
            assertEqual "Expected no new variable"
                Nothing
                (refreshVariable Set.empty setOriginal)

        , testCase "refreshVariable - avoid original" $
            assertBool
                "Expected fresh variable"
                (setOriginal < fresh0 setOriginal)

        , testCase "refreshVariable - avoid fresh" $
            assertBool
                "Expected another fresh variable"
                (fresh0 setOriginal < fresh1 setOriginal)
        ]

    , testGroup "instance FreshVariable (UnifiedVariable (ElementVariable Variable))"
        [ testCase "refreshVariable - avoid empty set" $
            assertEqual "Expected no new variable"
                Nothing
                (refreshVariable Set.empty elemOriginal)

        , testCase "refreshVariable - avoid original" $
            assertBool
                "Expected fresh variable"
                (unifiedElemOriginal < fresh0 unifiedElemOriginal)

        , testCase "refreshVariable - avoid fresh" $
            assertBool
                "Expected another fresh variable"
                (fresh0 unifiedElemOriginal < fresh1 unifiedElemOriginal)
        ]

    , testGroup "instance FreshVariable (UnifiedVariable (SetVariable Variable))"
        [ testCase "refreshVariable - avoid empty set" $
            assertEqual "Expected no new variable"
                Nothing
                (refreshVariable Set.empty unifiedSetOriginal)

        , testCase "refreshVariable - avoid original" $
            assertBool
                "Expected fresh variable"
                (unifiedSetOriginal < fresh0 unifiedSetOriginal)

        , testCase "refreshVariable - avoid fresh" $
            assertBool
                "Expected another fresh variable"
                (fresh0 unifiedSetOriginal < fresh1 unifiedSetOriginal)
        ]

    , testGroup "instance FreshVariable (ElementVariable (Target Variable))"
        [ testCase "refreshVariable - avoid empty set" $
            assertEqual "Expected no new variable"
                Nothing
                (refreshVariable Set.empty elemTargetOriginal)

        , testCase "refreshVariable - avoid original" $
            assertBool
                "Expected fresh variable"
                (elemTargetOriginal < fresh0 elemTargetOriginal)

        , testCase "refreshVariable - avoid original (ignore Target constructor)" $
            assertBool "Expected fresh variable"
                (elemTargetOriginal < fresh avoidET elemTargetOriginal)

        , testCase "refreshVariable - avoid fresh" $
            assertBool
                "Expected another fresh variable"
                (fresh0 elemTargetOriginal < fresh1 elemTargetOriginal)
        ]

    , testGroup "instance FreshVariable (SetVariable (Target Variable))"
        [ testCase "refreshVariable - avoid empty set" $
            assertEqual "Expected no new variable"
                Nothing
                (refreshVariable Set.empty setNonTargetOriginal)

        , testCase "refreshVariable - avoid original" $
            assertBool
                "Expected fresh variable"
                (setNonTargetOriginal < fresh0 setNonTargetOriginal)

        , testCase "refreshVariable - avoid original (ignore Target constructor)" $
            assertBool "Expected fresh variable"
                (setNonTargetOriginal < fresh avoidST setNonTargetOriginal)

        , testCase "refreshVariable - avoid fresh" $
            assertBool
                "Expected another fresh variable"
                (fresh0 setNonTargetOriginal < fresh1 setNonTargetOriginal)
        ]

    , testGroup "instance FreshVariable (UnifiedVariable (Target Variable))"
        [ testCase "refreshVariable - avoid empty set" $
            assertEqual "Expected no new variable"
                Nothing
                (refreshVariable Set.empty unifiedElemTargetOriginal)

        , testCase "refreshVariable - avoid original" $
            assertBool
                "Expected fresh variable"
                (unifiedElemTargetOriginal < fresh0 unifiedElemTargetOriginal)

        , testCase "refreshVariable - avoid original (ignore Target constructor)" $
            assertBool
                "Expected fresh variable"
                (unifiedElemTargetOriginal < fresh avoidUET unifiedElemTargetOriginal)

        , testCase "refreshVariable - avoid fresh" $
            assertBool
                "Expected another fresh variable"
                (fresh0 unifiedElemTargetOriginal < fresh1 unifiedElemTargetOriginal)
        , testCase "refreshVariable - avoid empty set" $
            assertEqual "Expected no new variable"
                Nothing
                (refreshVariable Set.empty unifiedSetNonTargetOriginal)

        , testCase "refreshVariable - avoid original" $
            assertBool
                "Expected fresh variable"
                (unifiedSetNonTargetOriginal < fresh0 unifiedSetNonTargetOriginal)

        , testCase "refreshVariable - avoid original (ignore Target constructor)" $
            assertBool
                "Expected fresh variable"
                (unifiedSetNonTargetOriginal < fresh avoidUST unifiedSetNonTargetOriginal)

        , testCase "refreshVariable - avoid fresh" $
            assertBool
                "Expected another fresh variable"
                (fresh0 unifiedSetNonTargetOriginal < fresh1 unifiedSetNonTargetOriginal)
        ]
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

    targetOriginal = Target original
    nonTargetOriginal = NonTarget original
    avoidT = Set.singleton nonTargetOriginal

    -- ElementVariable (Target Variable)
    elemTargetOriginal    = mkElementTarget elemOriginal
    elemNonTargetOriginal = mkElementNonTarget elemOriginal
    avoidET = Set.singleton elemNonTargetOriginal
    -- SetVariable (Target Variable)
    setTargetOriginal     = mkSetTarget setOriginal
    setNonTargetOriginal  = mkSetNonTarget setOriginal
    avoidST = Set.singleton setTargetOriginal

    unifiedTarget = mapUnifiedVariable (pure Target)

    unifiedNonTarget = mapUnifiedVariable (pure Target)

    -- UnifiedVariable (Target Variable)
    unifiedElemTargetOriginal, unifiedElemNonTargetOriginal,
        unifiedSetTargetOriginal, unifiedSetNonTargetOriginal
        :: UnifiedVariable (Target Variable)
    unifiedElemTargetOriginal    = unifiedTarget unifiedElemOriginal
    unifiedElemNonTargetOriginal = unifiedNonTarget unifiedElemOriginal
    unifiedSetTargetOriginal     = unifiedTarget  unifiedSetOriginal
    unifiedSetNonTargetOriginal  = unifiedNonTarget unifiedSetOriginal
    avoidUET = Set.singleton unifiedElemNonTargetOriginal
    avoidUST = Set.singleton unifiedSetTargetOriginal

{- | Property tests of a 'FreshPartialOrd' instance using the given generator.

The generator should produce a 'Pair' of related variables.

 -}
testFreshPartialOrd
    :: (Show variable, FreshPartialOrd variable)
    => Gen (Pair variable)
    -> [TestTree]
testFreshPartialOrd gen =
    [ testProperty "exclusive bounds" $ property $ do
        xy <- forAll gen
        let Pair infX infY = infVariable <$> xy
            Pair supX supY = supVariable <$> xy
        annotateShow infX
        annotateShow supX
        annotateShow infY
        annotateShow supY
        (infX == infY) === (supX == supY)
        infX /== supY
        infY /== supX
    , testProperty "lower and upper bound" $ property $ do
        Pair x _ <- forAll gen
        let inf = infVariable x
            sup = supVariable x
        annotateShow inf
        annotateShow sup
        Hedgehog.assert (inf <= x)
        Hedgehog.assert (x <= sup)
        Hedgehog.assert (inf < sup)
    , testProperty "idempotence" $ property $ do
        Pair x _ <- forAll gen
        let inf1 = infVariable x
            inf2 = infVariable inf1
            sup1 = supVariable x
            sup2 = supVariable sup1
        inf1 === inf2
        sup1 === sup2
    , testProperty "nextVariable" $ property $ do
        Pair x _ <- forAll gen
        let inf = infVariable x
            sup = supVariable x
            next = nextVariable x
        unless (x < sup) discard
        annotateShow inf
        annotateShow sup
        annotateShow next
        Hedgehog.assert (inf < next)
        Hedgehog.assert (x < next)
        Hedgehog.assert (next < sup)
    ]

test_FreshPartialOrd_Variable :: TestTree
test_FreshPartialOrd_Variable =
    testGroup "instance FreshPartialOrd Variable"
    $ testFreshPartialOrd relatedVariableGen

test_FreshPartialOrd_ElementVariable :: TestTree
test_FreshPartialOrd_ElementVariable =
    testGroup "instance FreshPartialOrd (ElementVariable Variable)"
    $ testFreshPartialOrd relatedElementVariableGen

test_FreshPartialOrd_SetVariable :: TestTree
test_FreshPartialOrd_SetVariable =
    testGroup "instance FreshPartialOrd (SetVariable Variable)"
    $ testFreshPartialOrd relatedSetVariableGen

test_FreshPartialOrd_UnifiedVariable :: TestTree
test_FreshPartialOrd_UnifiedVariable =
    testGroup "instance FreshPartialOrd (UnifiedVariable Variable)"
    $ testFreshPartialOrd relatedUnifiedVariableGen

relatedVariableGen :: Gen (Pair Variable)
relatedVariableGen = do
    Pair name1 name2 <-
        Gen.choice
            [ do { name <- idGen; return (Pair name name) }
            , Pair <$> idGen <*> idGen
            ]
    Pair counter1 counter2 <-
        Gen.choice
            [ do { counter <- counterGen; return (Pair counter counter) }
            , Pair <$> counterGen <*> counterGen
            ]
    Pair sort1 sort2 <-
        Gen.choice
            [ do { sort <- sortGen; return (Pair sort sort) }
            , Pair <$> sortGen <*> sortGen
            ]
    let variable1 = Variable name1 counter1 sort1
        variable2 = Variable name2 counter2 sort2
    return (Pair variable1 variable2)

counterGen :: MonadGen gen => gen (Maybe (Sup Natural))
counterGen =
    Gen.frequency
        [ (2, pure Nothing)
        , (4, Just . Element <$> Gen.integral (Range.linear 0 256))
        , (1, pure $ Just Sup)
        ]

sortGen :: MonadGen gen => gen Sort
sortGen = Gen.element [testSort, topSort, subSort]

relatedElementVariableGen :: Gen (Pair (ElementVariable Variable))
relatedElementVariableGen = (fmap . fmap) ElementVariable relatedVariableGen

relatedSetVariableGen :: Gen (Pair (SetVariable Variable))
relatedSetVariableGen = (fmap . fmap) SetVariable relatedVariableGen

relatedUnifiedVariableGen :: Gen (Pair (UnifiedVariable Variable))
relatedUnifiedVariableGen =
    Gen.choice
        [ (fmap . fmap) ElemVar relatedElementVariableGen
        , (fmap . fmap) SetVar relatedSetVariableGen
        ]

test_FreshPartialOrd_VariableName :: TestTree
test_FreshPartialOrd_VariableName =
    testGroup "instance FreshPartialOrd VariableName"
    $ testFreshPartialOrd relatedVariableNameGen

relatedVariableNameGen :: Gen (Pair VariableName)
relatedVariableNameGen = do
    Pair name1 name2 <-
        Gen.choice
            [ do { name <- idGen; return (Pair name name) }
            , Pair <$> idGen <*> idGen
            ]
    Pair counter1 counter2 <-
        Gen.choice
            [ do { counter <- counterGen; return (Pair counter counter) }
            , Pair <$> counterGen <*> counterGen
            ]
    let variable1 = VariableName name1 counter1
        variable2 = VariableName name2 counter2
    return (Pair variable1 variable2)

test_FreshPartialOrd_ElementVariableName :: TestTree
test_FreshPartialOrd_ElementVariableName =
    testGroup "instance FreshPartialOrd (ElementVariableName VariableName)"
    $ testFreshPartialOrd
    $ (fmap . fmap) ElementVariableName relatedVariableNameGen

test_FreshPartialOrd_SetVariableName :: TestTree
test_FreshPartialOrd_SetVariableName =
    testGroup "instance FreshPartialOrd (SetVariableName VariableName)"
    $ testFreshPartialOrd
    $ (fmap . fmap) SetVariableName relatedVariableNameGen

test_FreshPartialOrd_SomeVariableName :: TestTree
test_FreshPartialOrd_SomeVariableName =
    testGroup "instance FreshPartialOrd (SomeVariableName VariableName)"
    $ testFreshPartialOrd
    $ someVariableNameGen relatedVariableNameGen

someVariableNameGen
    :: Gen (Pair variable)
    -> Gen (Pair (SomeVariableName variable))
someVariableNameGen gen =
    Gen.choice
        [ (fmap . fmap) (inject . ElementVariableName) gen
        , (fmap . fmap) (inject . SetVariableName) gen
        ]
