module Test.Kore.Builtin.List where

import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty
import           Test.Tasty.HUnit

import qualified Data.Foldable as Foldable
import qualified Data.Reflection as Reflection
import           Data.Sequence
                 ( Seq )
import qualified Data.Sequence as Seq

import qualified Kore.AST.Kore as Kore
import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Attribute.Hook
                 ( Hook )
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import qualified Kore.Attribute.Symbol as StepperAttributes
import qualified Kore.Builtin.List as List
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.Pattern
import           Kore.Step.Representation.ExpandedPattern
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern

import           Test.Kore
                 ( testId )
import           Test.Kore.Builtin.Builtin
import           Test.Kore.Builtin.Definition
import qualified Test.Kore.Builtin.Int as Test.Int
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools )
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
        (===) ExpandedPattern.bottom =<< evaluate patGet
        (===) ExpandedPattern.top =<< evaluate predicate

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
            patList = asPattern (Test.Int.asInternal <$> values)
            value =
                case values of
                    Seq.Empty -> Nothing
                    v Seq.:<| _ -> Just v
            patFirst = maybe mkBottom_ Test.Int.asInternal value
            predicate = mkEquals_ patGet patFirst
        let expectGet = Test.Int.asPartialExpandedPattern value
        (===) expectGet =<< evaluate patGet
        (===) ExpandedPattern.top =<< evaluate predicate

test_getLastElement :: TestTree
test_getLastElement =
    testPropertyWithSolver
        "get{}(concat{}(_, element{}(e)), -1) === e"
        prop
  where
    prop = do
        values <- forAll genSeqInteger
        let patGet = mkApp intSort getListSymbol [ patList , Test.Int.asInternal (-1) ]
            patList = asPattern (Test.Int.asInternal <$> values)
            value =
                case values of
                    Seq.Empty -> Nothing
                    _ Seq.:|> v -> Just v
            patFirst = maybe mkBottom_ Test.Int.asInternal value
            predicate = mkEquals_ patGet patFirst
        let expectGet = Test.Int.asPartialExpandedPattern value
        (===) expectGet =<< evaluate patGet
        (===) ExpandedPattern.top =<< evaluate predicate

test_concatUnit :: TestTree
test_concatUnit =
    testPropertyWithSolver
        "concat{}(unit{}(), xs) === concat{}(xs, unit{}()) === xs"
        prop
  where
    prop = do
        values <- forAll genSeqInteger
        let patUnit = mkApp listSort unitListSymbol []
            patValues = asPattern (Test.Int.asInternal <$> values)
            patConcat1 = mkApp listSort concatListSymbol [ patUnit, patValues ]
            patConcat2 = mkApp listSort concatListSymbol [ patValues, patUnit ]
            predicate1 = mkEquals_ patValues patConcat1
            predicate2 = mkEquals_ patValues patConcat2
        expectValues <- evaluate patValues
        (===) expectValues =<< evaluate patConcat1
        (===) expectValues =<< evaluate patConcat2
        (===) ExpandedPattern.top =<< evaluate predicate1
        (===) ExpandedPattern.top =<< evaluate predicate2

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
        let patList1 = asPattern $ Test.Int.asInternal <$> values1
            patList2 = asPattern $ Test.Int.asInternal <$> values2
            patList3 = asPattern $ Test.Int.asInternal <$> values3
            patConcat12 = mkApp listSort concatListSymbol [ patList1, patList2 ]
            patConcat23 = mkApp listSort concatListSymbol [ patList2, patList3 ]
            patConcat12_3 =
                mkApp listSort concatListSymbol [ patConcat12, patList3 ]
            patConcat1_23 =
                mkApp listSort concatListSymbol [ patList1, patConcat23 ]
            predicate = mkEquals_ patConcat12_3 patConcat1_23
        evalConcat12_3 <- evaluate patConcat12_3
        evalConcat1_23 <- evaluate patConcat1_23
        (===) evalConcat12_3 evalConcat1_23
        (===) ExpandedPattern.top =<< evaluate predicate

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
            expected = asExpandedPattern [x]
        (===) expected =<< evaluate original

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

mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools
        Mock.attributesMapping
        Mock.headTypeMapping
        Mock.sortAttributesMapping
        Mock.subsorts

mockHookTools :: MetadataTools Object Hook
mockHookTools = StepperAttributes.hook <$> mockMetadataTools

-- | Specialize 'List.asPattern' to the builtin sort 'listSort'.
asPattern
    :: Foldable f
    => f (CommonStepPattern Object)
    -> CommonStepPattern Object
asPattern =
    Reflection.give testMetadataTools List.asPattern
    . builtinList
    . Foldable.toList

-- | Specialize 'List.asInternal' to the builtin sort 'listSort'.
asInternal
    :: Foldable f
    => f (CommonStepPattern Object)
    -> CommonStepPattern Object
asInternal =
    List.asInternal testMetadataTools listSort
    . Seq.fromList
    . Foldable.toList

-- | Specialize 'List.asExpandedPattern' to the builtin sort 'listSort'.
asExpandedPattern
    :: Foldable f
    => f (CommonStepPattern Object)
    -> CommonExpandedPattern Object
asExpandedPattern =
    Reflection.give testMetadataTools List.asExpandedPattern listSort
    . Seq.fromList
    . Foldable.toList

hprop_unparse :: Property
hprop_unparse =
    hpropUnparse (asInternal . (<$>) Test.Int.asInternal <$> genSeqInteger)
