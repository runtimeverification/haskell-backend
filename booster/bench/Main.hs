{-# LANGUAGE OverloadedRecordDot #-}

module Main (main) where

import BenchData
import Booster.Benchmark.Ops
import Booster.Pattern.Base
import Test.Tasty.Bench

main :: IO ()
main =
    defaultMain
        [ bgroup "kmap" (map kmapBenchFor benchmarkSizes)
        , bgroup "kset" (map ksetBenchFor benchmarkSizes)
        , bgroup "klist" (map klistBenchFor benchmarkSizes)
        , pipelineBenchmarks
        ]

kmapBenchFor :: Int -> Benchmark
kmapBenchFor size =
    let mapTerm = mkMapTerm size
        existingKey = mkLookupExistingKey size
        missingKey = mkLookupMissingKey size
        insertKey = mkInsertKey size
        insertValue = mkUpdatedValue (size + 1)
        updateValue = mkUpdatedValue (size + 2)
        duplicatePairs = case mapTerm of
            KMap _ pairs _ -> pairs <> reverse pairs
            _ -> []
        coreBenches =
            [ bench "lookup-existing" $ nf (runMapLookup mapTerm) existingKey
            , bench "lookup-missing" $ nf (runMapLookup mapTerm) missingKey
            , bench "size" $ nf runMapSize mapTerm
            ]
        heavyBenches =
            [ bench "insert" $ nf (\(m, k, v) -> runMapUpdate m k v) (mapTerm, insertKey, insertValue)
            , bench "update" $ nf (\(m, k, v) -> runMapUpdate m k v) (mapTerm, existingKey, updateValue)
            , bench "remove" $ nf (\(m, k) -> runMapRemove m k) (mapTerm, existingKey)
            , bench "keys" $ nf runMapKeys mapTerm
            , bench "values" $ nf runMapValues mapTerm
            , bench "in_keys" $ nf (runMapInKeys mapTerm) existingKey
            , bench "sortAndDeduplicate" $ nf (\pairs -> KMap benchmarkKMapDef pairs Nothing) duplicatePairs
            ]
     in bgroup
            ("size-" <> show size)
            (coreBenches <> whenSizeAtMost 10000 size heavyBenches)

ksetBenchFor :: Int -> Benchmark
ksetBenchFor size =
    let leftSet = mkSetTerm size
        rightSet = mkSetTerm (max 1 (size `div` 2))
        probe = mkSetElement (max 1 (size `div` 3))
        duplicateElements = case leftSet of
            KSet _ elements _ -> elements <> reverse elements
            _ -> []
        coreBenches =
            [ bench "in" $ nf (ksetIn probe) leftSet
            , bench "size" $ nf ksetSize leftSet
            ]
        heavyBenches =
            [ bench "difference" $ nf (\(l, r) -> ksetDifference l r) (leftSet, rightSet)
            , bench "union" $ nf (\(l, r) -> ksetUnion l r) (leftSet, rightSet)
            , bench "intersection" $ nf (\(l, r) -> ksetIntersection l r) (leftSet, rightSet)
            , bench "sortAndDeduplicate" $
                nf (\elements -> KSet benchmarkKSetDef elements Nothing) duplicateElements
            ]
     in bgroup
            ("size-" <> show size)
            (coreBenches <> whenSizeAtMost 10000 size heavyBenches)

klistBenchFor :: Int -> Benchmark
klistBenchFor size =
    let listTerm = mkListTerm size
        concatRhs = mkListConcatRhs size
        idxMiddle = size `div` 2
        idxLast = max 0 (size - 1)
        rangeTrim = max 0 (size `div` 4)
        coreBenches =
            [ bench "get-0" $ nf (runListGet listTerm) 0
            , bench "get-middle" $ nf (runListGet listTerm) idxMiddle
            , bench "get-last" $ nf (runListGet listTerm) idxLast
            , bench "size" $ nf runListSize listTerm
            ]
        heavyBenches =
            [ bench "range" $ nf (\(l, f, b) -> runListRange l f b) (listTerm, rangeTrim, rangeTrim)
            , bench "concat" $ nf (\(l, r) -> runListConcat l r) (listTerm, concatRhs)
            ]
     in bgroup
            ("size-" <> show size)
            (coreBenches <> whenSizeAtMost 10000 size heavyBenches)

pipelineBenchmarks :: Benchmark
pipelineBenchmarks =
    bgroup
        "pipeline"
        [ bgroup "kmap-matchMaps" (map mapMatchBenchFor matchMapBenchSizes)
        , bgroup "ord-term" (map ordBenchFor pipelineBenchSizes)
        , bgroup "substitution" (map substitutionBenchFor pipelineBenchSizes)
        , bench "full-single-rule-pipeline" $ nfIO runPipelineOnce
        ]

matchMapBenchSizes :: [Int]
matchMapBenchSizes = [10, 100, 1000]

pipelineBenchSizes :: [Int]
pipelineBenchSizes = [10, 100, 1000, 5000]

mapMatchBenchFor :: Int -> Benchmark
mapMatchBenchFor size =
    let patternMap = mkPatternMapForMatch size
        subjectMap = mkSubjectMapForMatch size
     in bgroup
            ("size-" <> show size)
            [ bench "matchMaps" $ whnf (\(p, s) -> matchMapTerms p s) (patternMap, subjectMap)
            ]

whenSizeAtMost :: Int -> Int -> [Benchmark] -> [Benchmark]
whenSizeAtMost limit size benchmarks
    | size <= limit = benchmarks
    | otherwise = []

ordBenchFor :: Int -> Benchmark
ordBenchFor size =
    let left = mkMapTerm size
        right =
            case mkMapTerm size of
                KMap def pairs rest ->
                    KMap def ((mkInsertKey (size + 7), mkUpdatedValue (size + 7)) : pairs) rest
                other -> other
     in bgroup
            ("size-" <> show size)
            [ bench "derived" $ whnf (\(a, b) -> compare a b) (left, right)
            , bench "hash-first" $ whnf (\(a, b) -> compareTermHashFirst a b) (left, right)
            ]

substitutionBenchFor :: Int -> Benchmark
substitutionBenchFor size =
    let unchangedKeyMap = mkMapWithValueVariables size
        unchangedKeySubst = mkValueSubstitution size
        changedKeyMap = mkMapWithKeyVariables size
        changedKeySubst = mkKeySubstitution size
     in bgroup
            ("size-" <> show size)
            [ bench "unchanged-keys" $
                nf (\(subst, term) -> substituteMap subst term) (unchangedKeySubst, unchangedKeyMap)
            , bench "changed-keys" $
                nf (\(subst, term) -> substituteMap subst term) (changedKeySubst, changedKeyMap)
            ]
