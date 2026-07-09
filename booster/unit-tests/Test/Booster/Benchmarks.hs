{- |
Copyright   : (c) Runtime Verification, 2026
License     : BSD-3-Clause
-}
module Test.Booster.Benchmarks (
    test_benchmarks,
) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit

import Booster.Benchmark.Data
import Booster.Benchmark.Ops
import Booster.Builtin.INT (intTerm)
import Booster.Pattern.Base
import Booster.Pattern.Match (MatchResult (..))

test_benchmarks :: TestTree
test_benchmarks =
    testGroup
        "Benchmark framework"
        [ generatorTests
        , mapOperationTests
        , setOperationTests
        , listOperationTests
        , pipelineTests
        ]

generatorTests :: TestTree
generatorTests =
    testGroup
        "Generator validity"
        [ testCase "KMap generator produces unique keys" $ do
            assertBool "invalid generated KMap" (validateKMap (mkMapTerm 100))
            case mkMapTerm 100 of
                KMap _ pairs Nothing -> length pairs @?= 100
                other -> assertFailure $ "expected concrete KMap, got: " <> show other
        , testCase "KSet generator produces sorted/de-duplicated elements" $ do
            assertBool "invalid generated KSet" (validateKSet (mkSetTerm 100))
            case mkSetTerm 100 of
                KSet _ elements Nothing -> length elements @?= 100
                other -> assertFailure $ "expected concrete KSet, got: " <> show other
        , testCase "KList generator preserves requested size" $ do
            assertBool "invalid generated KList" (validateKList (mkListTerm 100))
            case mkListTerm 100 of
                KList _ elements Nothing -> length elements @?= 100
                other -> assertFailure $ "expected concrete KList, got: " <> show other
        ]

mapOperationTests :: TestTree
mapOperationTests =
    testGroup
        "KMap operations"
        [ testCase "lookup finds existing keys and misses unknown keys" $ do
            let mapTerm = mkMapTerm 10
            runMapLookup mapTerm (mkMapKey 5) @?= Right (Just (mkMapValue 5))
            runMapLookup mapTerm (mkLookupMissingKey 10) @?= Right Nothing
        , testCase "update and insert via MAP.update are observable by lookup" $ do
            let mapTerm = mkMapTerm 10
                targetKey = mkMapKey 5
                updatedValue = mkUpdatedValue 10
                insertedKey = mkInsertKey 10
                insertedValue = mkUpdatedValue 11

            updated <- expectSomeTerm "MAP.update existing key" (runMapUpdate mapTerm targetKey updatedValue)
            runMapLookup updated targetKey @?= Right (Just updatedValue)

            inserted <- expectSomeTerm "MAP.update new key" (runMapUpdate mapTerm insertedKey insertedValue)
            runMapLookup inserted insertedKey @?= Right (Just insertedValue)
        , testCase "remove drops key from map" $ do
            let mapTerm = mkMapTerm 10
                targetKey = mkMapKey 3
            removed <- expectSomeTerm "MAP.remove" (runMapRemove mapTerm targetKey)
            runMapLookup removed targetKey @?= Right Nothing
        , testCase "matchMaps benchmark fixture succeeds" $ do
            case matchMapTerms (mkPatternMapForMatch 20) (mkSubjectMapForMatch 20) of
                MatchSuccess _ -> pure ()
                other -> assertFailure $ "expected MatchSuccess, got: " <> show other
        ]

setOperationTests :: TestTree
setOperationTests =
    testGroup
        "KSet operations"
        [ testCase "in and size" $ do
            let fullSet = mkSetTerm 10
            assertBool "expected membership" (ksetIn (mkSetElement 3) fullSet)
            ksetSize fullSet @?= 10
        , testCase "difference/union/intersection" $ do
            let fullSet = mkSetTerm 10
                subset = mkSetTerm 5
            ksetSize (ksetDifference fullSet subset) @?= 5
            ksetSize (ksetUnion fullSet subset) @?= 10
            ksetSize (ksetIntersection fullSet subset) @?= 5
        ]

listOperationTests :: TestTree
listOperationTests =
    testGroup
        "KList operations"
        [ testCase "get at front/middle/back" $ do
            let listTerm = mkListTerm 10
            runListGet listTerm 0 @?= Right (Just (mkListElement 1))
            runListGet listTerm 5 @?= Right (Just (mkListElement 6))
            runListGet listTerm 9 @?= Right (Just (mkListElement 10))
        , testCase "size/range/concat" $ do
            let listTerm = mkListTerm 10
                rhs = mkListConcatRhs 10
            runListSize listTerm @?= Right (Just (intTerm 10))
            runListRange listTerm 1 1
                @?= Right
                    ( Just
                        (KList benchmarkKListDef (map mkListElement [2 .. 9]) Nothing)
                    )
            concatenated <- expectSomeTerm "LIST.concat" (runListConcat listTerm rhs)
            runListSize concatenated @?= Right (Just (intTerm 20))
        ]

pipelineTests :: TestTree
pipelineTests =
    testGroup
        "Pipeline benchmark"
        [ testCase "full pipeline executes successfully" $ do
            outcome <- runPipelineOnce
            case outcome of
                Right renderedSize ->
                    assertBool "expected non-empty externalised output" (renderedSize > 0)
                Left err ->
                    assertFailure ("pipeline failed: " <> show err)
        ]

expectSomeTerm :: Show t => String -> Either t (Maybe Term) -> IO Term
expectSomeTerm label = \case
    Right (Just term) -> pure term
    Right Nothing -> do
        _ <- assertFailure (label <> " returned Nothing")
        error (label <> ": unreachable")
    Left err -> do
        _ <- assertFailure (label <> " returned Left error: " <> show err)
        error (label <> ": unreachable")
