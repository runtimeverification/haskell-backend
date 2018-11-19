module Test.Kore.Builtin.List where

import           Hedgehog hiding
                 ( property )
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty

import           Data.Reflection
                 ( give )
import           Data.Sequence
                 ( Seq )
import qualified Data.Sequence as Seq

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import qualified Kore.ASTUtils.SmartConstructors as Kore
import           Kore.ASTUtils.SmartPatterns
import qualified Kore.Builtin.List as List
import qualified Kore.Domain.Builtin as Domain
import           Kore.Step.ExpandedPattern
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Pattern

import           Test.Kore
                 ( testId )
import           Test.Kore.Builtin.Builtin
import           Test.Kore.Builtin.Definition
import qualified Test.Kore.Builtin.Int as Test.Int
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
                App_ getListSymbol
                    [ App_ unitListSymbol []
                    , Test.Int.asPattern k
                    ]
            predicate = mkEquals mkBottom patGet
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
        let patGet = App_ getListSymbol [ patList , Test.Int.asPattern 0 ]
            patList = asPattern (Test.Int.asPattern <$> values)
            value =
                case values of
                    Seq.Empty -> Nothing
                    v Seq.:<| _ -> Just v
            patFirst = maybe mkBottom Test.Int.asPattern value
            predicate = mkEquals patGet patFirst
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
        let patGet = App_ getListSymbol [ patList , Test.Int.asPattern (-1) ]
            patList = asPattern (Test.Int.asPattern <$> values)
            value =
                case values of
                    Seq.Empty -> Nothing
                    _ Seq.:|> v -> Just v
            patFirst = maybe mkBottom Test.Int.asPattern value
            predicate = give testSymbolOrAliasSorts $ mkEquals patGet patFirst
        let expectGet = Test.Int.asPartialExpandedPattern value
        (===) expectGet =<< evaluate patGet
        (===) ExpandedPattern.top =<< evaluate predicate

test_concatUnit :: TestTree
test_concatUnit =
    testPropertyWithSolver
        "concat{}(unit{}(), xs) === concat{}(xs, unit{}()) === xs"
        property
  where
    property = give testSymbolOrAliasSorts $ do
        values <- forAll genSeqInteger
        let patUnit = App_ unitListSymbol []
            patValues = asPattern (Test.Int.asPattern <$> values)
            patConcat1 = App_ concatListSymbol [ patUnit, patValues ]
            patConcat2 = App_ concatListSymbol [ patValues, patUnit ]
            predicate1 = mkEquals patValues patConcat1
            predicate2 = mkEquals patValues patConcat2
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
    property = give testSymbolOrAliasSorts $ do
        values1 <- forAll genSeqInteger
        values2 <- forAll genSeqInteger
        values3 <- forAll genSeqInteger
        let patList1 = asPattern $ Test.Int.asPattern <$> values1
            patList2 = asPattern $ Test.Int.asPattern <$> values2
            patList3 = asPattern $ Test.Int.asPattern <$> values3
            patConcat12 = App_ concatListSymbol [ patList1, patList2 ]
            patConcat23 = App_ concatListSymbol [ patList2, patList3 ]
            patConcat12_3 = App_ concatListSymbol [ patConcat12, patList3 ]
            patConcat1_23 = App_ concatListSymbol [ patList1, patConcat23 ]
            predicate = mkEquals patConcat12_3 patConcat1_23
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
                    , variableSort = intSort
                    }
            original =
                mkDomainValue listSort
                $ Domain.BuiltinList (Seq.fromList [mkAnd x mkTop])
            expected =
                ExpandedPattern.fromPurePattern
                $ mkDomainValue listSort
                $ Domain.BuiltinList (Seq.fromList [x])
        (===) expected =<< evaluate original

-- | Specialize 'List.asPattern' to the builtin sort 'listSort'.
asPattern :: List.Builtin Variable -> CommonStepPattern Object
Right asPattern = List.asPattern indexedModule listSort

-- | Specialize 'List.asPattern' to the builtin sort 'listSort'.
asExpandedPattern :: List.Builtin Variable -> CommonExpandedPattern Object
Right asExpandedPattern = List.asExpandedPattern indexedModule listSort

-- * Constructors

mkBottom :: CommonStepPattern Object
mkBottom = Kore.mkBottom

mkEquals
    :: CommonStepPattern Object
    -> CommonStepPattern Object
    -> CommonStepPattern Object
mkEquals = give testSymbolOrAliasSorts Kore.mkEquals

mkAnd
    :: CommonStepPattern Object
    -> CommonStepPattern Object
    -> CommonStepPattern Object
mkAnd = give testSymbolOrAliasSorts Kore.mkAnd

mkTop :: CommonStepPattern Object
mkTop = Kore.mkTop

mkVar :: Variable Object -> CommonStepPattern Object
mkVar = give testSymbolOrAliasSorts Kore.mkVar

mkDomainValue
    :: Sort Object
    -> Domain.Builtin (CommonStepPattern Object)
    -> CommonStepPattern Object
mkDomainValue = give testSymbolOrAliasSorts Kore.mkDomainValue
