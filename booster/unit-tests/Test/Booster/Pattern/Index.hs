{-# LANGUAGE QuasiQuotes #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Test.Booster.Pattern.Index (
    test_indexing,
) where

import Data.Set qualified as Set
import Test.Tasty
import Test.Tasty.HUnit

import Booster.Pattern.Base
import Booster.Pattern.Index (CellIndex (..), TermIndex (..))
import Booster.Pattern.Index qualified as Idx
import Booster.Syntax.Json.Internalise (trm)
import Booster.Syntax.ParsedKore.Internalise (symb)
import Test.Booster.Fixture hiding (inj)

test_indexing :: TestTree
test_indexing =
    testGroup
        "Term Indexing"
        [ testKCellIndexing
        , testCompositeIndexing
        , testTopTermIndexing
        , testIndexCover
        ]

testKCellIndexing :: TestTree
testKCellIndexing =
    testGroup
        "Indexing the K cell"
        [ testCase "An empty K cell is indexed as dotk" $
            [trm| kCell{}(dotk{}()) |] ==> TopCons "dotk"
        , testCase "A non-empty K cell is indexed as its head element without injections" $ do
            [trm| kCell{}(kseq{}(inj{SomeSort{},SortKItem{}}(f1{}(X:SomeSort{})), dotk{}())) |]
                ==> TopFun "f1"
            KSeq someSort [trm| X:SomeSort{} |]
                ==> Anything
            [trm| kCell{}(kseq{}(inj{SomeSort{},SortKItem{}}(\dv{SomeSort{}}("X")), dotk{}())) |]
                ==> Value "X"
            [trm| kCell{}(X:SortK{}) |]
                ==> Anything
        , testCase "The K cell is found when nested under other cells" $ do
            [trm|
                topCell{}(
                  nesting{}(
                    kCell{}(kseq{}(inj{SomeSort{},SortKItem{}}(f1{}(X:SomeSort{})), dotk{}()))
                  ),
                  other{}(dotk{}())
                )
                |]
                ==> TopFun "f1"
            [trm|
                topCell{}(
                  nesting{}(
                    kCell{}(dotk{}())
                  ),
                  other{}(X:SortK{})
                )
                |]
                ==> TopCons "dotk"
        ]
  where
    (==>) :: Term -> CellIndex -> Assertion
    t ==> result = Idx.kCellTermIndex t @=? TermIndex [result]

kCell, other, topCell, nesting, inj :: Symbol
kCell = [symb| symbol Lbl'-LT-'k'-GT-'{}(SortK{}) : SortKCell{} [constructor{}()] |]
other = [symb| symbol Lbl'-LT-'other'-GT-'{}(SortK{}) : SomeSort{} [constructor{}()] |]
topCell = [symb| symbol Lbl'-LT-'topCell'-GT-'{}(SomeSort{}, SomeSort{}) : SomeSort{} [constructor{}()] |]
nesting = [symb| symbol Lbl'-LT-'nesting'-GT-'{}(SortKCell{}) : SomeSort{} [constructor{}()] |]
inj = [symb| symbol inj{From, To}( From ) : To [sortInjection{}()] |]

testCompositeIndexing :: TestTree
testCompositeIndexing =
    testGroup
        "Indexing with custom cells"
        [ testCase "No cells for indexing results in empty index" $
            Idx.compositeTermIndex [] undefined @?= TermIndex []
        , testCase "The desired cell is found when nested under other cells" $ do
            testWith
                [other.name]
                [trm|
                    topCell{}(
                      nesting{}(
                        kCell{}(kseq{}(inj{SomeSort{},SortKItem{}}(f1{}(X:SomeSort{})), dotk{}()))
                      ),
                      other{}(dotk{}())
                    )
                    |]
                [TopCons "dotk"]
            testWith
                [other.name]
                [trm|
                    topCell{}(
                      nesting{}(
                        kCell{}(dotk{}())
                      ),
                      other{}(
                        kseq{}(inj{SomeSort{},SortKItem{}}(f1{}(X:SomeSort{})), dotk{}())
                      )
                    )
                    |]
                [TopFun "f1"]
            testWith
                [other.name]
                [trm|
                    topCell{}(
                      nesting{}(
                        kCell{}(dotk{}())
                      ),
                      other{}(X:SortK{})
                    )
                    |]
                [Anything]
        , testCase "Two cells can be chosen" $ do
            testWith
                [other.name, kCell.name]
                [trm|
                    topCell{}(
                      nesting{}(
                        kCell{}(kseq{}(inj{SomeSort{},SortKItem{}}(f1{}(X:SomeSort{})), dotk{}()))
                      ),
                      other{}(dotk{}())
                    )
                    |]
                [TopCons "dotk", TopFun "f1"]
            testWith
                [other.name, kCell.name]
                [trm|
                    topCell{}(
                      nesting{}(
                        kCell{}(X:SortK{})
                      ),
                      other{}(
                        kseq{}(inj{SomeSort{},SortKItem{}}(f1{}(X:SomeSort{})), dotk{}())
                      )
                    )
                    |]
                [TopFun "f1", Anything]
            testWith
                [other.name, kCell.name]
                [trm|
                    topCell{}(
                      nesting{}(
                        kCell{}(dotk{}())
                      ),
                      other{}(X:SortK{})
                    )
                    |]
                [Anything, TopCons "dotk"]
        , testCase "If a duplicated cell is chosen, the first occurrence counts" $ do
            testWith
                [other.name]
                [trm|
                    topCell{}(
                      other{}(X:SortK{}),
                      other{}(dotk{}())
                    )
                    |]
                [Anything]
            testWith
                [other.name]
                [trm|
                    topCell{}(
                      other{}(dotk{}()),
                      other{}(X:SortK{})
                    )
                    |]
                [TopCons "dotk"]
        ]
  where
    testWith :: [SymbolName] -> Term -> [CellIndex] -> Assertion
    testWith cells term result = Idx.compositeTermIndex cells term @=? TermIndex result

testTopTermIndexing :: TestTree
testTopTermIndexing =
    testGroup
        "Indexing the top term"
        [ testCase "Different terms get different indexes" $ do
            [trm| VAR:SomeSort{} |] ==> Anything
            [trm| \dv{SomeSort{}}("") |] ==> Value ""
            [trm| f1{}(VAR:SomeSort{}) |] ==> TopFun "f1"
            [trm| con1{}(VAR:SomeSort{}) |] ==> TopCons "con1"
            KMap testKMapDefinition [] Nothing ==> TopMap
            KList testKListDef [] Nothing ==> TopList
            KSet testKSetDef [] Nothing ==> TopSet
        , testCase "And-terms are indexed by combining the argument indexes" $ do
            AndTerm [trm| f1{}( X:SomeSort{} ) |] [trm| Y:SomeSort{} |] ==> TopFun "f1"
            AndTerm [trm| X:SomeSort{} |] [trm| con1{}( Y:SomeSort{} ) |] ==> TopCons "con1"
            AndTerm [trm| f1{}( X:SomeSort{} ) |] [trm| f1{}( Y:SomeSort{} ) |] ==> TopFun "f1"
            AndTerm [trm| f1{}( X:SomeSort{} ) |] [trm| f2{}( Y:SomeSort{} ) |] ==> None
            AndTerm [trm| X:SomeSort{} |] [trm| Y:SomeSort{} |] ==> Anything
        ]
  where
    (==>) :: Term -> CellIndex -> Assertion
    t ==> result = Idx.termTopIndex t @?= TermIndex [result]

testIndexCover :: TestTree
testIndexCover =
    testGroup
        "Index covering function"
        [ testCase "indexes function works" $ do
            indexes 0 @=? Set.singleton (TermIndex [])
            indexes 1 @=? Set.fromList [TermIndex [i] | i <- cellIndexes]
            indexes 2 @=? Set.fromList [TermIndex [i, j] | i <- cellIndexes, j <- cellIndexes]
        , --  , testCase "Anything in all components is unchanged" $
          --    [Anything, Anything, Anything] ==> [[Anything, Anything, Anything]]
          testCase "[Anything] is added to single-component indexes" $
            [TopCons "bla"] ==> [[TopCons "bla"], [Anything]]
        , testCase "Anything is added to every component, in all combinations" $ do
            let cells = map TopCons ["bla", "blu", "bli"]
            take 2 cells
                ==> [ [TopCons "bla", TopCons "blu"]
                    , [TopCons "bla", Anything]
                    , [Anything, TopCons "blu"]
                    , [Anything, Anything]
                    ]
            cells
                ==> [ cells
                    , [TopCons "bla", TopCons "blu", Anything]
                    , [TopCons "bla", Anything, TopCons "bli"]
                    , [TopCons "bla", Anything, Anything]
                    , [Anything, TopCons "blu", TopCons "bli"]
                    , [Anything, TopCons "blu", Anything]
                    , [Anything, Anything, TopCons "bli"]
                    , [Anything, Anything, Anything]
                    ]
        , testCase "Term index [Anything] is covered by all possible indexes" $ do
            [Anything] ==> map (: []) cellIndexes
        ]
  where
    (==>) :: [CellIndex] -> [[CellIndex]] -> Assertion
    idx ==> expected =
        (indexes (length idx) `Idx.covering` TermIndex idx)
            @?= Set.fromList (map TermIndex expected)
    cellIndexes =
        map TopCons ["bla", "blu", "bli"]
            <> map TopFun ["f1", "f2"]
            <> [TopMap, TopList, TopSet, Anything]
    indexes = Set.fromList . map TermIndex . permuteCIs
    permuteCIs n
        | n <= 0 = [[]]
        | otherwise = [i : is | i <- cellIndexes, is <- permuteCIs (n - 1)]
