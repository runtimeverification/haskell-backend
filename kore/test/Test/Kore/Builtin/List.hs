module Test.Kore.Builtin.List where

import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty
import           Test.Tasty.HUnit

import qualified Control.Monad.Trans as Trans
import qualified Data.Foldable as Foldable
import qualified Data.Reflection as Reflection
import           Data.Sequence
                 ( Seq )
import qualified Data.Sequence as Seq

import           Kore.Attribute.Hook
                 ( Hook )
import qualified Kore.Attribute.Symbol as StepperAttributes
import qualified Kore.Builtin.List as List
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike

import           Test.Kore
                 ( testId )
import           Test.Kore.Builtin.Builtin
import           Test.Kore.Builtin.Definition
import qualified Test.Kore.Builtin.Int as Test.Int
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.SMT

genInteger :: Gen Integer
genInteger = Gen.integral (Range.linear (-1024) 1024)

genSeqInteger :: Gen (Seq Integer)
genSeqInteger = Gen.seq (Range.linear 0 16) genInteger

test_getUnit :: TestTree
test_getUnit =
    testPropertyWithSolver "get{}(unit{}(), _) === \\bottom{}()" $ do
        k <- forAll genInteger
        let patGet =
                mkApp intSort getListSymbol
                    [ mkApp listSort unitListSymbol []
                    , Test.Int.asInternal k
                    ]
            predicate = mkEquals_ mkBottom_ patGet
        (===) Pattern.bottom =<< Trans.lift (evaluate patGet)
        (===) Pattern.top    =<< Trans.lift (evaluate predicate)

test_getFirstElement :: TestTree
test_getFirstElement =
    testPropertyWithSolver
        "get{}(concat{}(element{}(e), _), 0) === e"
        prop
  where
    prop = do
        values <- forAll genSeqInteger
        let patGet =
                mkApp intSort getListSymbol [ patList , Test.Int.asInternal 0 ]
            patList = asTermLike (Test.Int.asInternal <$> values)
            value =
                case values of
                    Seq.Empty -> Nothing
                    v Seq.:<| _ -> Just v
            patFirst = maybe mkBottom_ Test.Int.asInternal value
            predicate = mkEquals_ patGet patFirst
        let expectGet = Test.Int.asPartialPattern value
        (===) expectGet   =<< Trans.lift (evaluate patGet)
        (===) Pattern.top =<< Trans.lift (evaluate predicate)

test_getLastElement :: TestTree
test_getLastElement =
    testPropertyWithSolver
        "get{}(concat{}(_, element{}(e)), -1) === e"
        prop
  where
    prop = do
        values <- forAll genSeqInteger
        let patGet =
                mkApp
                    intSort
                    getListSymbol
                    [ patList , Test.Int.asInternal (-1) ]
            patList = asTermLike (Test.Int.asInternal <$> values)
            value =
                case values of
                    Seq.Empty -> Nothing
                    _ Seq.:|> v -> Just v
            patFirst = maybe mkBottom_ Test.Int.asInternal value
            predicate = mkEquals_ patGet patFirst
        let expectGet = Test.Int.asPartialPattern value
        (===) expectGet   =<< Trans.lift (evaluate patGet)
        (===) Pattern.top =<< Trans.lift (evaluate predicate)

test_concatUnit :: TestTree
test_concatUnit =
    testPropertyWithSolver
        "concat{}(unit{}(), xs) === concat{}(xs, unit{}()) === xs"
        prop
  where
    prop = do
        values <- forAll genSeqInteger
        let patUnit = mkApp listSort unitListSymbol []
            patValues = asTermLike (Test.Int.asInternal <$> values)
            patConcat1 = mkApp listSort concatListSymbol [ patUnit, patValues ]
            patConcat2 = mkApp listSort concatListSymbol [ patValues, patUnit ]
            predicate1 = mkEquals_ patValues patConcat1
            predicate2 = mkEquals_ patValues patConcat2
        expectValues <- Trans.lift $ evaluate patValues
        (===) expectValues =<< Trans.lift (evaluate patConcat1)
        (===) expectValues =<< Trans.lift (evaluate patConcat2)
        (===) Pattern.top  =<< Trans.lift (evaluate predicate1)
        (===) Pattern.top  =<< Trans.lift (evaluate predicate2)

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
            patConcat12 = mkApp listSort concatListSymbol [ patList1, patList2 ]
            patConcat23 = mkApp listSort concatListSymbol [ patList2, patList3 ]
            patConcat12_3 =
                mkApp listSort concatListSymbol [ patConcat12, patList3 ]
            patConcat1_23 =
                mkApp listSort concatListSymbol [ patList1, patConcat23 ]
            predicate = mkEquals_ patConcat12_3 patConcat1_23
        evalConcat12_3 <- Trans.lift $ evaluate patConcat12_3
        evalConcat1_23 <- Trans.lift $ evaluate patConcat1_23
        (===) evalConcat12_3 evalConcat1_23
        (===) Pattern.top =<< Trans.lift (evaluate predicate)

-- | Check that simplification is carried out on list elements.
test_simplify :: TestTree
test_simplify =
    testPropertyWithSolver "simplify elements" $ do
        let
            x =
                mkVar Variable
                    { variableName = testId "x"
                    , variableCounter = mempty
                    , variableSort = intSort
                    }
            original = asInternal [mkAnd x mkTop_]
            expected = asPattern [x]
        (===) expected =<< Trans.lift (evaluate original)

test_isBuiltin :: [TestTree]
test_isBuiltin =
    [ testCase "isSymbolConcat" $ do
        assertBool ""
            (List.isSymbolConcat mockHookTools Mock.concatListSymbol)
        assertBool ""
            (not (List.isSymbolConcat mockHookTools Mock.aSymbol))
        assertBool ""
            (not (List.isSymbolConcat mockHookTools Mock.elementListSymbol))
    , testCase "isSymbolElement" $ do
        assertBool ""
            (List.isSymbolElement mockHookTools Mock.elementListSymbol)
        assertBool ""
            (not (List.isSymbolElement mockHookTools Mock.aSymbol))
        assertBool ""
            (not (List.isSymbolElement mockHookTools Mock.concatListSymbol))
    , testCase "isSymbolUnit" $ do
        assertBool ""
            (List.isSymbolUnit mockHookTools Mock.unitListSymbol)
        assertBool ""
            (not (List.isSymbolUnit mockHookTools Mock.aSymbol))
        assertBool ""
            (not (List.isSymbolUnit mockHookTools Mock.concatListSymbol))
    ]

mockHookTools :: SmtMetadataTools Hook
mockHookTools = StepperAttributes.hook <$> Mock.metadataTools

-- | Specialize 'List.asPattern' to the builtin sort 'listSort'.
asTermLike
    :: Foldable f
    => f (TermLike Variable)
    -> TermLike Variable
asTermLike =
    Reflection.give testMetadataTools List.asTermLike
    . builtinList
    . Foldable.toList

-- | Specialize 'List.asInternal' to the builtin sort 'listSort'.
asInternal
    :: Foldable f
    => f (TermLike Variable)
    -> TermLike Variable
asInternal =
    List.asInternal testMetadataTools listSort
    . Seq.fromList
    . Foldable.toList

-- | Specialize 'List.asPattern' to the builtin sort 'listSort'.
asPattern
    :: Foldable f
    => f (TermLike Variable)
    -> Pattern Variable
asPattern =
    Reflection.give testMetadataTools List.asPattern listSort
    . Seq.fromList
    . Foldable.toList

hprop_unparse :: Property
hprop_unparse =
    hpropUnparse (asInternal . (<$>) Test.Int.asInternal <$> genSeqInteger)
