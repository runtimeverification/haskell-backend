{-# LANGUAGE QuasiQuotes #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Test.Booster.Pattern.Index (
    test_indexing,
) where

import Test.Tasty
import Test.Tasty.HUnit

import Booster.Definition.Attributes.Base
import Booster.Definition.Base
import Booster.Pattern.Base
import Booster.Pattern.Index (TermIndex (..), CellIndex (..))
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
        ]

testKCellIndexing :: TestTree
testKCellIndexing =
    testGroup
        "Indexing the K cell"
        [ testCase "An empty K cell is indexed as dotk" $
            [trm| kCell{}(dotk{}()) |] ==> TopSymbol "dotk"
        , testCase "A non-empty K cell is indexed as its head element without injections" $ do
            KSeq someSort [trm| X:SomeSort{} |]
                ==> Anything
            [trm| kCell{}(kseq{}(inj{SomeSort{},SortKItem{}}(\dv{SomeSort{}}("X")), dotk{}())) |]
                ==> Anything
            [trm| kCell{}(kseq{}(inj{SomeSort{},SortKItem{}}(f1{}(X:SomeSort{})), dotk{}())) |]
                ==> TopSymbol "f1"
        ]
  where
    kCell :: Symbol
    kCell =
        [symb| symbol Lbl'-LT-'k'-GT-'{}(SortK{}) : SortKCell{} [constructor{}()] |]

    (==>) :: Term -> CellIndex -> Assertion
    t ==> result = Idx.kCellTermIndex t @=? TermIndex [result]

inj :: Symbol
inj = [symb| symbol inj{From, To}( From ) : To [sortInjection{}()] |]

testCompositeIndexing :: TestTree
testCompositeIndexing =
    testGroup
        "Indexing with custom cells"
        [ testCase "No cells for indexing results in empty index" $
            Idx.compositeTermIndex [] undefined @=? TermIndex []
        ]

testTopTermIndexing :: TestTree
testTopTermIndexing =
    testGroup
        "Indexing the top term"
        [ testCase "Only symbol applications get an index" $ do
            [trm| VAR:SomeSort{} |] ==> Anything
            [trm| \dv{SomeSort{}}("") |] ==> Anything
            [trm| f1{}(VAR:SomeSort{}) |] ==> TopSymbol "f1"
        , testCase "And-terms are indexed by combining the argument indexes" $ do
            AndTerm [trm| f1{}( X:SomeSort{} ) |] [trm| Y:SomeSort{} |] ==> TopSymbol "f1"
            AndTerm [trm| X:SomeSort{} |] [trm| f1{}( Y:SomeSort{} ) |] ==> TopSymbol "f1"
            AndTerm [trm| f1{}( X:SomeSort{} ) |] [trm| f1{}( Y:SomeSort{} ) |] ==> TopSymbol "f1"
            AndTerm [trm| f1{}( X:SomeSort{} ) |] [trm| f2{}( Y:SomeSort{} ) |] ==> None
            AndTerm [trm| X:SomeSort{} |] [trm| Y:SomeSort{} |] ==> Anything
        ]
  where
    (==>) :: Term -> CellIndex -> Assertion
    t ==> result = Idx.termTopIndex t @=? TermIndex [result]
