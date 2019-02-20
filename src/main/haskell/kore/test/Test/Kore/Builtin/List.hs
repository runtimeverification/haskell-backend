module Test.Kore.Builtin.List where

import           Hedgehog hiding
                 ( property )
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty
import           Test.Tasty.HUnit

import           Data.Sequence
                 ( Seq )
import qualified Data.Sequence as Seq

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Attribute.Hook
                 ( Hook )
import qualified Kore.Builtin.List as List
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.ExpandedPattern
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Pattern
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Step.StepperAttributes as StepperAttributes

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
    testPropertyWithSolver
        "get{}(unit{}(), _) === \\bottom{}()"
        property
  where
    property = do
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
        property
  where
    property = do
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
        property
  where
    property = do
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
        property
  where
    property = do
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
        property
  where
    property = do
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
    testPropertyWithSolver
        "simplify elements"
        property
  where
    property = do
        let
            x =
                mkVar Variable
                    { variableName = testId "x"
                    , variableCounter = mempty
                    , variableSort = intSort
                    }
            original =
                mkDomainValue listSort
                $ Domain.BuiltinList (Seq.fromList [mkAnd x mkTop_])
            expected =
                ExpandedPattern.fromPurePattern
                $ mkDomainValue listSort
                $ Domain.BuiltinList (Seq.fromList [x])
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
asPattern :: List.Builtin Variable -> CommonStepPattern Object
Right asPattern = List.asPattern verifiedModule listSort

-- | Specialize 'List.asPattern' to the builtin sort 'listSort'.
asExpandedPattern :: List.Builtin Variable -> CommonExpandedPattern Object
Right asExpandedPattern = List.asExpandedPattern verifiedModule listSort
