module Test.Kore.Builtin.List (
    test_getUnit,
    test_getFirstElement,
    test_getLastElement,
    test_GetUpdate,
    test_concatUnit,
    test_concatUnitSymbolic,
    test_concatAssociates,
    test_concatSymbolic,
    test_concatSymbolicDifferentLengths,
    test_simplify,
    test_isBuiltin,
    test_inUnit,
    test_inElement,
    test_inConcat,
    test_make,
    test_updateAll,
    hprop_unparse,
    test_size,
    --
    asInternal,
    asTermLike,
    genSeqInteger,
) where

import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import qualified Data.Reflection as Reflection
import Data.Sequence (
    Seq,
 )
import qualified Data.Sequence as Seq
import Data.Text (
    Text,
 )
import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import qualified Kore.Builtin.List as List
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    makeTruePredicate,
 )
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    configElementVariableFromId,
 )
import Prelude.Kore
import Test.Kore (
    testId,
 )
import qualified Test.Kore.Builtin.Bool as Test.Bool
import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import qualified Test.Kore.Builtin.Int as Test.Int
import qualified Test.Kore.Internal.OrPattern as OrPattern
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.SMT
import Test.Tasty
import Test.Tasty.HUnit

genInteger :: Gen Integer
genInteger = Gen.integral (Range.linear (-1024) 1024)

genSeqInteger :: Gen (Seq Integer)
genSeqInteger = Gen.seq (Range.linear 0 16) genInteger

genSeqIndex :: Gen Integer
genSeqIndex = Gen.integral (Range.linear (-20) 20)

test_getUnit :: TestTree
test_getUnit =
    testPropertyWithSolver "get{}(unit{}(), _) === \\bottom{}()" $ do
        k <- forAll genInteger
        let patGet =
                mkApplySymbol
                    getListSymbol
                    [ mkApplySymbol unitListSymbol []
                    , Test.Int.asInternal k
                    ]
            predicate = mkEquals_ mkBottom_ patGet
        (===) OrPattern.bottom =<< evaluateT patGet
        (===) OrPattern.top =<< evaluateT predicate

test_getFirstElement :: TestTree
test_getFirstElement =
    testPropertyWithSolver
        "get{}(concat{}(element{}(e), _), 0) === e"
        prop
  where
    prop = do
        values <- forAll genSeqInteger
        let patGet =
                mkApplySymbol getListSymbol [patList, Test.Int.asInternal 0]
            patList :: TermLike RewritingVariableName
            patList = asTermLike (Test.Int.asInternal <$> values)
            value =
                case values of
                    Seq.Empty -> Nothing
                    v Seq.:<| _ -> Just v
            patFirst = maybe mkBottom_ Test.Int.asInternal value
            predicate = mkEquals_ patGet patFirst
        let expectGet = Test.Int.asPartialPattern value
        (===) (MultiOr.singleton expectGet) =<< evaluateT patGet
        (===) OrPattern.top =<< evaluateT predicate

test_getLastElement :: TestTree
test_getLastElement =
    testPropertyWithSolver
        "get{}(concat{}(_, element{}(e)), -1) === e"
        prop
  where
    prop = do
        values <- forAll genSeqInteger
        let patGet =
                mkApplySymbol
                    getListSymbol
                    [patList, Test.Int.asInternal (-1)]
            patList = asTermLike (Test.Int.asInternal <$> values)
            value =
                case values of
                    Seq.Empty -> Nothing
                    _ Seq.:|> v -> Just v
            patFirst = maybe mkBottom_ Test.Int.asInternal value
            predicate = mkEquals_ patGet patFirst
        let expectGet = Test.Int.asPartialPattern value
        (===) (MultiOr.singleton expectGet) =<< evaluateT patGet
        (===) OrPattern.top =<< evaluateT predicate

test_GetUpdate :: TestTree
test_GetUpdate =
    testPropertyWithSolver
        "get{}(update{}(map, ix, val), ix) === val"
        prop
  where
    prop = do
        values <- forAll genSeqInteger
        value <- forAll Test.Int.genIntegerPattern
        ix <- forAll genSeqIndex
        let len = fromIntegral $ length values
            patValues = asTermLike $ Test.Int.asInternal <$> values
            patUpdated = updateList patValues (Test.Int.asInternal ix) value
        if 0 <= ix && ix < len
            then do
                let patGet = getList patUpdated $ Test.Int.asInternal ix
                    predicate =
                        mkEquals_
                            patGet
                            value
                    expect = Pattern.fromTermLike value
                (===) OrPattern.top =<< evaluateT predicate
                (===) (MultiOr.singleton expect) =<< evaluateT patGet
            else do
                let predicate = mkEquals_ mkBottom_ patUpdated
                (===) OrPattern.bottom =<< evaluateT patUpdated
                (===) OrPattern.top =<< evaluateT predicate

test_inUnit :: TestTree
test_inUnit =
    testPropertyWithSolver
        "in{}(x, unit{}()) === \\dv{Bool{}}(\"false\")"
        prop
  where
    prop = do
        value <- forAll genInteger
        let patValue = Test.Int.asInternal value
            patIn = inList patValue unitList
            patFalse = Test.Bool.asInternal False
            predicate = mkEquals_ patFalse patIn
        (===) (Test.Bool.asOrPattern False) =<< evaluateT patIn
        (===) OrPattern.top =<< evaluateT predicate

test_inElement :: TestTree
test_inElement =
    testPropertyWithSolver
        "in{}(x, element{}(x)) === \\dv{Bool{}}(\"true\")"
        prop
  where
    prop = do
        value <- forAll genInteger
        let patValue = Test.Int.asInternal value
            patElement = elementList patValue
            patIn = inList patValue patElement
            patTrue = Test.Bool.asInternal True
            predicate = mkEquals_ patIn patTrue
        (===) (Test.Bool.asOrPattern True) =<< evaluateT patIn
        (===) OrPattern.top =<< evaluateT predicate

test_inConcat :: TestTree
test_inConcat =
    testPropertyWithSolver
        "in{}(x, concat{}(list, element{}(x))) === \\dv{Bool{}}(\"true\")"
        prop
  where
    prop = do
        value <- forAll genInteger
        values <- forAll genSeqInteger
        let patValue = Test.Int.asInternal value
            patValues = asTermLike (Test.Int.asInternal <$> values)
            patElement = elementList patValue
            patConcat = concatList patValues patElement
            patIn = inList patValue patConcat
            patTrue = Test.Bool.asInternal True
            predicate = mkEquals_ patIn patTrue
        (===) (Test.Bool.asOrPattern True) =<< evaluateT patIn
        (===) OrPattern.top =<< evaluateT predicate

test_concatUnit :: TestTree
test_concatUnit =
    testPropertyWithSolver
        "concat{}(unit{}(), xs) === concat{}(xs, unit{}()) === xs"
        prop
  where
    prop = do
        values <- forAll genSeqInteger
        let patUnit = mkApplySymbol unitListSymbol []
            patValues = asTermLike (Test.Int.asInternal <$> values)
            patConcat1 = mkApplySymbol concatListSymbol [patUnit, patValues]
            patConcat2 = mkApplySymbol concatListSymbol [patValues, patUnit]
            predicate1 = mkEquals_ patValues patConcat1
            predicate2 = mkEquals_ patValues patConcat2
        expectValues <- evaluateT patValues
        (===) expectValues =<< evaluateT patConcat1
        (===) expectValues =<< evaluateT patConcat2
        (===) OrPattern.top =<< evaluateT predicate1
        (===) OrPattern.top =<< evaluateT predicate2

test_concatUnitSymbolic :: TestTree
test_concatUnitSymbolic =
    testPropertyWithSolver
        "concat{}(unit{}(), x) === concat{}(xs, unit{}()) === x"
        prop
  where
    prop = do
        let patUnit = mkApplySymbol unitListSymbol []
            patSymbolic =
                mkElemVar $ configElementVariableFromId (testId "x") listSort
            patConcat1 = mkApplySymbol concatListSymbol [patUnit, patSymbolic]
            patConcat2 = mkApplySymbol concatListSymbol [patSymbolic, patUnit]
            predicate1 = mkEquals_ patSymbolic patConcat1
            predicate2 = mkEquals_ patSymbolic patConcat2
        expectSymbolic <- evaluateT patSymbolic
        (===) expectSymbolic =<< evaluateT patConcat1
        (===) expectSymbolic =<< evaluateT patConcat2
        (===) OrPattern.top =<< evaluateT predicate1
        (===) OrPattern.top =<< evaluateT predicate2

test_concatAssociates :: TestTree
test_concatAssociates =
    testPropertyWithSolver
        "concat{}(concat{}(as, bs), cs) === concat{}(as, concat{}(bs, cs))"
        prop
  where
    prop = do
        values1 <- forAll genSeqInteger
        values2 <- forAll genSeqInteger
        values3 <- forAll genSeqInteger
        let patList1 = asTermLike $ Test.Int.asInternal <$> values1
            patList2 = asTermLike $ Test.Int.asInternal <$> values2
            patList3 = asTermLike $ Test.Int.asInternal <$> values3
            patConcat12 = mkApplySymbol concatListSymbol [patList1, patList2]
            patConcat23 = mkApplySymbol concatListSymbol [patList2, patList3]
            patConcat12_3 =
                mkApplySymbol concatListSymbol [patConcat12, patList3]
            patConcat1_23 =
                mkApplySymbol concatListSymbol [patList1, patConcat23]
            predicate = mkEquals_ patConcat12_3 patConcat1_23
        evalConcat12_3 <- evaluateT patConcat12_3
        evalConcat1_23 <- evaluateT patConcat1_23
        (===) evalConcat12_3 evalConcat1_23
        (===) OrPattern.top =<< evaluateT predicate

test_concatSymbolic :: TestTree
test_concatSymbolic =
    testPropertyWithSolver
        "concat{}(element{}(x), xs) === concat{}(element{}(y), ys))\n\
        \concat{}(xs, element{}(x)) === concat{}(ys, element{}(y))"
        prop
  where
    prop = do
        let elemVarX = "x" `ofSort` intSort
            patSymbolicX = mkElemVar elemVarX
            patSymbolicY = mkElemVar $ "y" `ofSort` intSort
            elemVarXs = "xs" `ofSort` listSort
            patSymbolicXs = mkElemVar elemVarXs
            patSymbolicYs = mkElemVar $ "ys" `ofSort` listSort
            patElemX =
                List.internalize testMetadataTools $ elementList patSymbolicX
            patElemY =
                List.internalize testMetadataTools $ elementList patSymbolicY

            patConcatX = concatList patElemX patSymbolicXs
            patConcatY = concatList patElemY patSymbolicYs
            patUnifiedXY = mkAnd patConcatX patConcatY

            expect =
                Conditional
                    { term = patConcatY
                    , predicate = makeTruePredicate
                    , substitution =
                        from @(Map (SomeVariable RewritingVariableName) _)
                            ( Map.fromList
                                [ (inject elemVarX, patSymbolicY)
                                , (inject elemVarXs, patSymbolicYs)
                                ]
                            )
                    }
                    & MultiOr.singleton
        unified <- evaluateT patUnifiedXY
        expect === unified

        let patConcatX' = concatList patSymbolicXs patElemX
            patConcatY' = concatList patSymbolicYs patElemY
            patUnifiedXY' = mkAnd patConcatX' patConcatY'

            expect' =
                Conditional
                    { term = patConcatY'
                    , predicate = makeTruePredicate
                    , substitution =
                        from @(Map (SomeVariable RewritingVariableName) _)
                            ( Map.fromList
                                [ (inject elemVarX, patSymbolicY)
                                , (inject elemVarXs, patSymbolicYs)
                                ]
                            )
                    }
                    & MultiOr.singleton
        unified' <- evaluateT patUnifiedXY'
        expect' === unified'

test_concatSymbolicDifferentLengths :: TestTree
test_concatSymbolicDifferentLengths =
    testPropertyWithSolver
        "concat{}(concat{}(element{}(x1), element{}(x2)), xs)\
        \ === concat{}(element{}(y), ys))"
        prop
  where
    prop = do
        let elemVarX1 = "x1" `ofSort` intSort
            patSymbolicX1 = mkElemVar elemVarX1
            patSymbolicX2 = mkElemVar $ "x2" `ofSort` intSort
            patSymbolicY = mkElemVar $ "y" `ofSort` intSort
            patSymbolicXs = mkElemVar $ "xs" `ofSort` listSort
            elemVarYs = "ys" `ofSort` listSort
            patSymbolicYs = mkElemVar elemVarYs
            patElemX1 =
                List.internalize testMetadataTools $ elementList patSymbolicX1
            patElemX2 =
                List.internalize testMetadataTools $ elementList patSymbolicX2
            patElemY =
                List.internalize testMetadataTools $ elementList patSymbolicY
            patConcatX =
                patElemX1 `concatList` patElemX2 `concatList` patSymbolicXs
            patConcatY = patElemY `concatList` patSymbolicYs
            patUnifiedXY = mkAnd patConcatX patConcatY
            expect =
                Conditional
                    { term =
                        patElemY
                            `concatList` (patElemX2 `concatList` patSymbolicXs)
                    , predicate = makeTruePredicate
                    , substitution =
                        from @(Map (SomeVariable RewritingVariableName) _)
                            ( Map.fromList
                                [ (inject elemVarX1, patSymbolicY)
                                ,
                                    ( inject elemVarYs
                                    , patElemX2 `concatList` patSymbolicXs
                                    )
                                ]
                            )
                    }
                    & MultiOr.singleton
        unified <- evaluateT patUnifiedXY
        expect === unified

ofSort :: Text -> Sort -> ElementVariable RewritingVariableName
ofSort name sort =
    configElementVariableFromId (testId name) sort

-- | Check that simplification is carried out on list elements.
test_simplify :: TestTree
test_simplify =
    testPropertyWithSolver "simplify elements" $ do
        let x = mkElemVar (configElementVariableFromId (testId "x") intSort)
            original = asInternal [mkAnd x mkTop_]
            expected = MultiOr.singleton $ asPattern [x]
        (===) expected =<< evaluateT original

test_isBuiltin :: [TestTree]
test_isBuiltin =
    [ testCase "isSymbolConcat" $ do
        assertBool "" (List.isSymbolConcat Mock.concatListSymbol)
        assertBool "" (not (List.isSymbolConcat Mock.aSymbol))
        assertBool "" (not (List.isSymbolConcat Mock.elementListSymbol))
    , testCase "isSymbolElement" $ do
        assertBool "" (List.isSymbolElement Mock.elementListSymbol)
        assertBool "" (not (List.isSymbolElement Mock.aSymbol))
        assertBool "" (not (List.isSymbolElement Mock.concatListSymbol))
    , testCase "isSymbolUnit" $ do
        assertBool "" (List.isSymbolUnit Mock.unitListSymbol)
        assertBool "" (not (List.isSymbolUnit Mock.aSymbol))
        assertBool "" (not (List.isSymbolUnit Mock.concatListSymbol))
    ]

test_size :: [TestTree]
test_size =
    [ testPropertyWithSolver "size(unit(_)) = 0" $ do
        let original = sizeList unitList
            zero = mkInt 0
            predicate = mkEquals_ zero original
        (===) (OrPattern.fromTermLike zero) =<< evaluateT original
        (===) OrPattern.top =<< evaluateT predicate
    , testPropertyWithSolver "size(element(_)) = 1" $ do
        k <- forAll genInteger
        let original = sizeList (elementList $ mkInt k)
            one = mkInt 1
            predicate = mkEquals_ one original
        (===) (OrPattern.fromTermLike one) =<< evaluateT original
        (===) OrPattern.top =<< evaluateT predicate
    , testPropertyWithSolver "size(a + b) = size(a) + size(b)" $ do
        as <- asInternal . fmap mkInt <$> forAll genSeqInteger
        bs <- asInternal . fmap mkInt <$> forAll genSeqInteger
        let sizeConcat = sizeList (concatList as bs)
            addSize = addInt (sizeList as) (sizeList bs)
            predicate = mkEquals_ sizeConcat addSize
        expect1 <- evaluateT sizeConcat
        expect2 <- evaluateT addSize
        (===) expect1 expect2
        (===) OrPattern.top =<< evaluateT predicate
    ]

test_make :: [TestTree]
test_make =
    [ testCaseWithoutSMT "make(-1, 5) === \\bottom" $ do
        result <- evaluate $ makeList (mkInt (-1)) (mkInt 5)
        assertEqual' "" OrPattern.bottom result
    , testCaseWithoutSMT "make(0, 5) === []" $ do
        result <- evaluate $ makeList (mkInt 0) (mkInt 5)
        assertEqual'
            ""
            (OrPattern.fromTermLike $ asInternal [])
            result
    , testCaseWithoutSMT "make(3, 5) === [5, 5, 5]" $ do
        result <- evaluate $ makeList (mkInt 3) (mkInt 5)
        let expect = asInternal . fmap mkInt $ Seq.fromList [5, 5, 5]
        assertEqual' "" (OrPattern.fromTermLike expect) result
    ]

test_updateAll :: [TestTree]
test_updateAll =
    [ testCaseWithoutSMT "updateAll([1, 2, 3], -1, [5]) === \\bottom" $ do
        result <-
            evaluate $
                updateAllList original (mkInt (-1)) (elementList $ mkInt 5)
        assertEqual' "" OrPattern.bottom result
    , testCaseWithoutSMT "updateAll([1, 2, 3], 10, []) === [1, 2, 3]" $ do
        result <-
            evaluate $
                updateAllList original (mkInt 10) unitList
        assertEqual' "" (OrPattern.fromTermLike original) result
    , testCaseWithoutSMT "updateAll([1, 2, 3], 1, [5]) === [1, 5, 3]" $ do
        result <-
            evaluate $
                updateAllList original (mkInt 1) (elementList $ mkInt 5)
        let expect = asInternal . fmap mkInt $ Seq.fromList [1, 5, 3]
        assertEqual' "" (OrPattern.fromTermLike expect) result
    , testCaseWithoutSMT "updateAll([1, 2, 3], 0, [1, 2, 3, 4]) === \\bottom" $
        do
            let new = asInternal . fmap mkInt $ Seq.fromList [1, 2, 3, 4]
            result <-
                evaluate $
                    updateAllList original (mkInt 0) new
            assertEqual' "" OrPattern.bottom result
    ]
  where
    original = asInternal . fmap mkInt $ Seq.fromList [1, 2, 3]

-- | Specialize 'List.asPattern' to the builtin sort 'listSort'.
asTermLike ::
    InternalVariable variable =>
    Foldable f =>
    f (TermLike variable) ->
    TermLike variable
asTermLike = asInternal

-- | Specialize 'List.asInternal' to the builtin sort 'listSort'.
asInternal ::
    InternalVariable variable =>
    Foldable f =>
    f (TermLike variable) ->
    TermLike variable
asInternal =
    List.asInternal testMetadataTools listSort
        . Seq.fromList
        . toList

-- | Specialize 'List.asPattern' to the builtin sort 'listSort'.
asPattern ::
    Foldable f =>
    f (TermLike RewritingVariableName) ->
    Pattern RewritingVariableName
asPattern =
    Reflection.give testMetadataTools List.asPattern listSort
        . Seq.fromList
        . toList

hprop_unparse :: Property
hprop_unparse =
    hpropUnparse (asInternal . (<$>) Test.Int.asInternal <$> genSeqInteger)
