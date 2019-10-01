module Test.Kore.Proof.Value where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Map as Map
import qualified GHC.Stack as GHC

import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin.Bool as Builtin.Bool
import qualified Kore.Builtin.Int as Builtin.Int
import qualified Kore.Domain.Builtin as Domain
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    )
import Kore.Internal.Symbol
    ( applicationSorts
    , toSymbolOrAlias
    )
import Kore.Internal.TermLike
import qualified Kore.Proof.Value as Value

import Test.Kore
import Test.Kore.Builtin.Definition
    ( boolSort
    , builtinList
    , builtinMap
    , builtinSet
    , intSort
    )
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
import qualified Test.Kore.Step.MockSymbols as Mock

unit_constructorUnit :: Assertion
unit_constructorUnit = assertValue unitPattern

unit_DomainValue :: Assertion
unit_DomainValue = assertValue oneTermLike

test_Builtin_InternalInt :: [TestTree]
test_Builtin_InternalInt =
    [ testValue "1" oneInternal
    , testValue "0" zeroInternal
    ]

test_Builtin_InternalBool :: [TestTree]
test_Builtin_InternalBool =
    [ testValue "true" trueInternal
    , testValue "false" falseInternal
    ]

unit_injConstructor :: Assertion
unit_injConstructor = assertValue (mkInj unitPattern)

unit_injInj :: Assertion
unit_injInj = assertNotValue (mkInj (mkInj unitPattern))

unit_pairConstructor :: Assertion
unit_pairConstructor = assertValue (mkPair unitPattern unitPattern)

test_Pair_Builtin :: [TestTree]
test_Pair_Builtin =
    [ testValue "(0, 0)" (mkPair zeroInternal zeroInternal)
    , testValue "(0, 1)" (mkPair zeroInternal oneInternal)
    , testValue "(1, 1)" (mkPair oneInternal  oneInternal)
    , testValue "(1, 0)" (mkPair oneInternal  zeroInternal)
    ]

test_Pair_DomainValue :: [TestTree]
test_Pair_DomainValue =
    [ testValue "(0, 0)" (mkPair zeroTermLike zeroTermLike)
    , testValue "(0, 1)" (mkPair zeroTermLike oneTermLike)
    , testValue "(1, 1)" (mkPair oneTermLike  oneTermLike)
    , testValue "(1, 0)" (mkPair oneTermLike  zeroTermLike)
    ]

test_Builtin_InternalMap :: [TestTree]
test_Builtin_InternalMap =
    [ testValue "0 |-> 1" (mkMap [(zeroInternal, oneInternal)])
    , testNotValue "0 |-> X" (mkMap [(zeroInternal, mkElemVar varX)])
    ]

test_Builtin_InternalList :: [TestTree]
test_Builtin_InternalList =
    [ testValue "[1]" (mkList [oneInternal])
    , testNotValue "[X]" (mkList [mkElemVar varX])
    ]

test_Builtin_InternalSet :: [TestTree]
test_Builtin_InternalSet =
    [ testValue "[1]" (mkSet [oneInternal])
    ]

varX :: ElementVariable Variable
varX = elemVarS "X" intSort

test_fun :: [TestTree]
test_fun =
    [ testNotValue "fun(1)" (mkApplySymbol funSymbol [oneTermLike])
    , testNotValue "fun(1)" (mkApplySymbol funSymbol [oneInternal])
    ]

mkInj :: TermLike Variable -> TermLike Variable
mkInj input = mkApplySymbol (injSymbol (termLikeSort input) supSort) [input]

mkPair
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
mkPair a b = mkApplySymbol (pairSymbol inputSort') [a, b]
  where
    inputSort' = termLikeSort a

mkMap :: [(TermLike Concrete, TermLike Variable)] -> TermLike Variable
mkMap = mkBuiltin . Domain.BuiltinMap . builtinMap

mkList :: [TermLike Variable] -> TermLike Variable
mkList = mkBuiltin . Domain.BuiltinList . builtinList

mkSet :: [TermLike Concrete] -> TermLike Variable
mkSet = mkBuiltin . Domain.BuiltinSet . builtinSet

unitPattern :: TermLike Variable
unitPattern = mkApplySymbol unitSymbol []

oneInternal :: Ord variable => TermLike variable
oneInternal = Builtin.Int.asInternal intSort 1

zeroInternal :: Ord variable => TermLike variable
zeroInternal = Builtin.Int.asInternal intSort 0

oneTermLike :: TermLike Variable
oneTermLike =
    Builtin.Int.asTermLike Domain.InternalInt
        { builtinIntSort = intSort
        , builtinIntValue = 1
        }

zeroTermLike :: TermLike Variable
zeroTermLike =
    Builtin.Int.asTermLike Domain.InternalInt
        { builtinIntSort = intSort
        , builtinIntValue = 0
        }

trueInternal :: TermLike Variable
trueInternal = Builtin.Bool.asInternal boolSort True

falseInternal :: TermLike Variable
falseInternal = Builtin.Bool.asInternal boolSort False

unitSort :: Sort
unitSort =
    SortActualSort SortActual
        { sortActualName = testId "Unit"
        , sortActualSorts = []
        }

unitSymbol :: Symbol
unitSymbol =
    Symbol
        { symbolConstructor = testId "unit"
        , symbolParams = []
        , symbolAttributes = Mock.constructorAttributes
        , symbolSorts = applicationSorts [] unitSort
        }

pairSort :: Sort -> Sort
pairSort sort =
    SortActualSort SortActual
        { sortActualName = testId "Pair"
        , sortActualSorts = [sort]
        }

pairSymbol :: Sort -> Symbol
pairSymbol sort =
    Symbol
        { symbolConstructor = testId "pair"
        , symbolParams = [sort]
        , symbolAttributes = Mock.constructorAttributes
        , symbolSorts = applicationSorts [sort, sort] (pairSort sort)
        }

injSymbol :: Sort -> Sort -> Symbol
injSymbol sub sup =
    Symbol
        { symbolConstructor = testId "inj"
        , symbolParams = [sub, sup]
        , symbolAttributes = Mock.sortInjectionAttributes
        , symbolSorts = applicationSorts [sub] sup
        }

funSymbol :: Symbol
funSymbol =
    Symbol
        { symbolConstructor = testId "fun"
        , symbolParams = []
        , symbolAttributes = Mock.functionAttributes
        , symbolSorts = applicationSorts [intSort] intSort
        }

subSort :: Sort
subSort = (SortVariableSort . SortVariable) (testId "sub")

supSort :: Sort
supSort = (SortVariableSort . SortVariable) (testId "sup")

symbolOrAliasAttrs :: [(SymbolOrAlias, Attribute.Symbol)]
symbolOrAliasAttrs =
    map ((,) <$> toSymbolOrAlias <*> symbolAttributes) symbols

symbols :: [Symbol]
symbols =
    [ unitSymbol
    , injSymbol subSort supSort
    , injSymbol unitSort supSort
    , injSymbol supSort supSort
    , pairSymbol unitSort
    , pairSymbol intSort
    , funSymbol
    ]

tools :: SmtMetadataTools Attribute.Symbol
tools =
    Mock.makeMetadataTools
        symbolOrAliasAttrs
        []
        []
        []
        Mock.emptySmtDeclarations
        Map.empty

assertValue :: GHC.HasCallStack => TermLike Variable -> Assertion
assertValue termLike =
    assertEqual "Expected normalized pattern"
        concrete
        (concrete >>= roundTrip)
  where
    concrete = asConcrete termLike
    roundTrip patt = do
        value <- Value.fromTermLike patt
        return (Value.asTermLike value)

testValue :: GHC.HasCallStack => TestName -> TermLike Variable -> TestTree
testValue name = testCase name . assertValue

assertNotValue :: GHC.HasCallStack => TermLike Variable -> Assertion
assertNotValue purePattern =
    assertEqual "Unexpected normalized pattern"
        Nothing
        (concretePattern >>= Value.fromTermLike)
  where
    concretePattern = asConcrete purePattern

testNotValue :: GHC.HasCallStack => TestName -> TermLike Variable -> TestTree
testNotValue name = testCase name . assertNotValue
