{-# LANGUAGE QuasiQuotes #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Test.Booster.Pattern.Index (
    test_indexing,
    test_equationIndex,
) where

import Control.Monad (replicateM)
import Data.Set qualified as Set
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)
import Test.Tasty.Hedgehog

import Booster.Pattern.Base
import Booster.Pattern.Index (CellIndex (..), TermIndex (..))
import Booster.Pattern.Index qualified as Idx
import Booster.Pattern.Match (MatchResult (..), MatchType (..), matchTerms)
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
            [trm| kCell{}(dotk{}()) |] ==> IdxCons "dotk"
        , testCase "A non-empty K cell is indexed as its head element without injections" $ do
            [trm| kCell{}(kseq{}(inj{SomeSort{},SortKItem{}}(f1{}(X:SomeSort{})), dotk{}())) |]
                ==> IdxFun "f1"
            KSeq someSort [trm| X:SomeSort{} |]
                ==> Anything
            [trm| kCell{}(kseq{}(inj{SomeSort{},SortKItem{}}(\dv{SomeSort{}}("X")), dotk{}())) |]
                ==> IdxVal "X"
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
                ==> IdxFun "f1"
            [trm|
                topCell{}(
                  nesting{}(
                    kCell{}(dotk{}())
                  ),
                  other{}(X:SortK{})
                )
                |]
                ==> IdxCons "dotk"
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
                [IdxCons "dotk"]
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
                [IdxFun "f1"]
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
                [IdxCons "dotk", IdxFun "f1"]
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
                [IdxFun "f1", Anything]
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
                [Anything, IdxCons "dotk"]
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
                [IdxCons "dotk"]
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
            [trm| \dv{SomeSort{}}("") |] ==> IdxVal ""
            [trm| f1{}(VAR:SomeSort{}) |] ==> IdxFun "f1"
            [trm| con1{}(VAR:SomeSort{}) |] ==> IdxCons "con1"
            KMap testKMapDefinition [] Nothing ==> IdxMap
            KList testKListDef [] Nothing ==> IdxList
            KSet testKSetDef [] Nothing ==> IdxSet
        , testCase "And-terms are indexed by combining the argument indexes" $ do
            AndTerm [trm| f1{}( X:SomeSort{} ) |] [trm| Y:SomeSort{} |] ==> IdxFun "f1"
            AndTerm [trm| X:SomeSort{} |] [trm| con1{}( Y:SomeSort{} ) |] ==> IdxCons "con1"
            AndTerm [trm| f1{}( X:SomeSort{} ) |] [trm| f1{}( Y:SomeSort{} ) |] ==> IdxFun "f1"
            AndTerm [trm| f1{}( X:SomeSort{} ) |] [trm| f2{}( Y:SomeSort{} ) |] ==> IdxNone
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
            [IdxCons "bla"] ==> [[IdxCons "bla"], [Anything]]
        , testCase "Anything is added to every component, in all combinations" $ do
            let cells = map IdxCons ["bla", "blu", "bli"]
            take 2 cells
                ==> [ [IdxCons "bla", IdxCons "blu"]
                    , [IdxCons "bla", Anything]
                    , [Anything, IdxCons "blu"]
                    , [Anything, Anything]
                    ]
            cells
                ==> [ cells
                    , [IdxCons "bla", IdxCons "blu", Anything]
                    , [IdxCons "bla", Anything, IdxCons "bli"]
                    , [IdxCons "bla", Anything, Anything]
                    , [Anything, IdxCons "blu", IdxCons "bli"]
                    , [Anything, IdxCons "blu", Anything]
                    , [Anything, Anything, IdxCons "bli"]
                    , [Anything, Anything, Anything]
                    ]
        , testCase "Cell index Anything is covered by all possible indexes" $ do
            [Anything] ==> map (: []) cellIndexes
            [Anything, IdxList] ==> concat [[[i, IdxList], [i, Anything]] | i <- cellIndexes]
            [Anything, Anything] ==> permuteCIs 2
        ]
  where
    (==>) :: [CellIndex] -> [[CellIndex]] -> Assertion
    idx ==> expected =
        (indexes (length idx) `Idx.covering` TermIndex idx)
            @?= Set.fromList (map TermIndex expected)
    cellIndexes =
        map IdxCons ["bla", "blu", "bli"]
            <> map IdxFun ["f1", "f2"]
            <> [IdxMap, IdxList, IdxSet, Anything]
    indexes = Set.fromList . map TermIndex . permuteCIs
    permuteCIs :: Int -> [[CellIndex]]
    permuteCIs n
        | n <= 0 = [[]]
        | otherwise = [i : is | i <- cellIndexes, is <- permuteCIs (n - 1)]

----------------------------------------
-- Depth-1 equation indexing

test_equationIndex :: TestTree
test_equationIndex =
    testGroup
        "Depth-1 equation indexing"
        [ testComponentTables
        , testIndexMatchContract
        ]

-- | The compatibility check 'applyEquations' uses to filter candidates
indexCompatible :: Idx.EquationTheory -> Term -> Term -> Bool
indexCompatible theory pat subj =
    Idx.invert (Idx.equationSubjectIndex theory subj) Idx.^<=^ Idx.equationLhsIndex theory pat

testComponentTables :: TestTree
testComponentTables =
    testGroup
        "Component behaviour per theory"
        [ testCase "Bare subject variable arguments rule out non-variable patterns for simplifications only" $ do
            -- pattern f1(con1(Y)) can never _match_ subject f1(X) ...
            incompatible Idx.Simplifications [trm| f1{}(con1{}(Y:SomeSort{})) |] [trm| f1{}(X:SomeSort{}) |]
            -- ... but the pair is indeterminate, so function equations must attempt it
            compatible Idx.FunctionEquations [trm| f1{}(con1{}(Y:SomeSort{})) |] [trm| f1{}(X:SomeSort{}) |]
        , testCase "Function-application pattern argument vs domain value: skippable for simplifications only" $ do
            incompatible
                Idx.Simplifications
                [trm| f1{}(f2{}(Y:SomeSort{})) |]
                [trm| f1{}(\dv{SomeSort{}}("0")) |]
            compatible
                Idx.FunctionEquations
                [trm| f1{}(f2{}(Y:SomeSort{})) |]
                [trm| f1{}(\dv{SomeSort{}}("0")) |]
        , testCase "Constructor mismatch in arguments is decisive for both theories" $ do
            incompatible
                Idx.Simplifications
                [trm| f1{}(con1{}(Y:SomeSort{})) |]
                [trm| f1{}(con2{}(X:SomeSort{})) |]
            incompatible
                Idx.FunctionEquations
                [trm| f1{}(con1{}(Y:SomeSort{})) |]
                [trm| f1{}(con2{}(X:SomeSort{})) |]
        , testCase "Variable pattern arguments cover any subject argument" $ do
            compatible Idx.Simplifications [trm| f1{}(Y:SomeSort{}) |] [trm| f1{}(X:SomeSort{}) |]
            compatible Idx.Simplifications [trm| f1{}(Y:SomeSort{}) |] [trm| f1{}(con1{}(X:SomeSort{})) |]
            compatible Idx.FunctionEquations [trm| f1{}(Y:SomeSort{}) |] [trm| f1{}(\dv{SomeSort{}}("0")) |]
        , testCase "Different head symbols are incompatible regardless of arguments" $ do
            incompatible Idx.Simplifications [trm| f1{}(X:SomeSort{}) |] [trm| f2{}(X:SomeSort{}) |]
            incompatible Idx.FunctionEquations [trm| f1{}(X:SomeSort{}) |] [trm| f2{}(X:SomeSort{}) |]
        ]
  where
    compatible theory pat subj =
        assertBool "expected index-compatible pair" (indexCompatible theory pat subj)
    incompatible theory pat subj =
        assertBool "expected index-incompatible pair" (not $ indexCompatible theory pat subj)

{- | Pins the index component tables to the matcher, row by row: if
the index allows skipping a (pattern, subject) pair, the match must
not have been able to return the result the skip would suppress.
-}
testIndexMatchContract :: TestTree
testIndexMatchContract =
    testGroup
        "Index skip-safety against matchTerms Eval"
        [ testProperty "a pair skipped by the simplification index can never match" . property $ do
            (pat, subj) <- forAll genTermPair
            cover 10 "incompatible" (not $ indexCompatible Idx.Simplifications pat subj)
            case matchTerms Eval testDefinition pat subj of
                MatchSuccess _ -> assert (indexCompatible Idx.Simplifications pat subj)
                _ -> pure ()
        , testProperty "a pair skipped by the function-equation index always fails decisively" . property $ do
            (pat, subj) <- forAll genTermPair
            cover 5 "incompatible" (not $ indexCompatible Idx.FunctionEquations pat subj)
            case matchTerms Eval testDefinition pat subj of
                MatchFailed _ -> pure ()
                -- successful and indeterminate matches must have been attempted
                _ -> assert (indexCompatible Idx.FunctionEquations pat subj)
        ]

genTermPair :: Gen (Term, Term)
genTermPair = do
    sym <- Gen.element [con1, con2, con3, f1, f2]
    let arity = length sym.argSorts
    pat <- app sym <$> replicateM arity (genArg 2)
    subj <- app sym <$> replicateM arity (genArg 2)
    pure (pat, subj)
  where
    genArg :: Int -> Gen Term
    genArg 0 =
        Gen.choice
            [ (`var` someSort) <$> Gen.element ["X", "Y", "Z"]
            , DomainValue someSort <$> Gen.element ["a", "b"]
            ]
    genArg n =
        Gen.frequency
            [ (3, genArg 0)
            , (2, (\c a -> app c [a]) <$> Gen.element [con1, con2] <*> genArg (n - 1))
            , (1, (\a b -> app con3 [a, b]) <$> genArg (n - 1) <*> genArg (n - 1))
            , (2, (\f a -> app f [a]) <$> Gen.element [f1, f2] <*> genArg (n - 1))
            ,
                ( 1
                , Injection aSubsort someSort . (\(a, b) -> app con4 [a, b])
                    <$> ((,) <$> genArg (n - 1) <*> genArg (n - 1))
                )
            , (1, pure (KMap testKMapDefinition [] Nothing))
            , (1, AndTerm <$> genArg (n - 1) <*> genArg (n - 1))
            ]
