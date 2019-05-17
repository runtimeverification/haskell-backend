module Test.Kore.Proof.Value where

import Test.Tasty
import Test.Tasty.HUnit

import qualified GHC.Stack as GHC

import           Kore.Attribute.Symbol
import qualified Kore.Builtin.Bool as Builtin.Bool
import qualified Kore.Builtin.Int as Builtin.Int
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( HeadType, SmtMetadataTools )
import qualified Kore.IndexedModule.MetadataTools as HeadType
                 ( HeadType (..) )
import           Kore.Internal.TermLike
import qualified Kore.Proof.Value as Value

import           Test.Kore
import           Test.Kore.Builtin.Definition
                 ( boolSort, builtinList, builtinMap, builtinSet, intSort )
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
    , testValue "fales" falseInternal
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
    , testNotValue "0 |-> X" (mkMap [(zeroInternal, mkVar varX)])
    ]

test_Builtin_InternalList :: [TestTree]
test_Builtin_InternalList =
    [ testValue "[1]" (mkList [oneInternal])
    , testNotValue "[X]" (mkList [mkVar varX])
    ]

test_Builtin_InternalSet :: [TestTree]
test_Builtin_InternalSet =
    [ testValue "[1]" (mkSet [oneInternal])
    ]

varX :: Variable
varX = varS "X" intSort

test_fun :: [TestTree]
test_fun =
    [ testNotValue "fun(1)" (mkApp intSort funSymbol [oneTermLike])
    , testNotValue "fun(1)" (mkApp intSort funSymbol [oneInternal])
    ]

mkInj :: TermLike Variable -> TermLike Variable
mkInj input =
    mkApp supSort (injSymbol (termLikeSort input) supSort) [input]

mkPair
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
mkPair a b =
    mkApp (pairSort inputSort') (pairSymbol inputSort') [a, b]
  where
    inputSort' = termLikeSort a

mkMap :: [(TermLike Concrete, TermLike Variable)] -> TermLike Variable
mkMap = mkBuiltin . Domain.BuiltinMap . builtinMap

mkList :: [TermLike Variable] -> TermLike Variable
mkList = mkBuiltin . Domain.BuiltinList . builtinList

mkSet :: [TermLike Concrete] -> TermLike Variable
mkSet = mkBuiltin . Domain.BuiltinSet . builtinSet

unitPattern :: TermLike Variable
unitPattern = mkApp unitSort unitSymbol []

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

unitSymbol :: SymbolOrAlias
unitSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = testId "unit"
        , symbolOrAliasParams = []
        }

pairSort :: Sort -> Sort
pairSort sort =
    SortActualSort SortActual
        { sortActualName = testId "Pair"
        , sortActualSorts = [sort]
        }

pairSymbol :: Sort -> SymbolOrAlias
pairSymbol sort =
    SymbolOrAlias
        { symbolOrAliasConstructor = testId "pair"
        , symbolOrAliasParams = [sort]
        }

injSymbol :: Sort -> Sort -> SymbolOrAlias
injSymbol sub sup =
    SymbolOrAlias
        { symbolOrAliasConstructor = testId "inj"
        , symbolOrAliasParams = [sub, sup]
        }

funSymbol :: SymbolOrAlias
funSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = testId "fun"
        , symbolOrAliasParams = []
        }

subSort :: Sort
subSort = (SortVariableSort . SortVariable) (testId "sub")

supSort :: Sort
supSort = (SortVariableSort . SortVariable) (testId "sup")

symbolOrAliasAttrs :: [(SymbolOrAlias, StepperAttributes)]
symbolOrAliasAttrs =
    [ (unitSymbol, Mock.constructorAttributes)
    , (injSymbol subSort supSort, Mock.sortInjectionAttributes)
    , (injSymbol unitSort supSort, Mock.sortInjectionAttributes)
    , (injSymbol supSort supSort, Mock.sortInjectionAttributes)
    , (pairSymbol unitSort, Mock.constructorAttributes)
    , (pairSymbol intSort, Mock.constructorAttributes)
    , (funSymbol, Mock.functionAttributes)
    ]

symbolOrAliasType :: [(SymbolOrAlias, HeadType)]
symbolOrAliasType =
    [ (unitSymbol, HeadType.Symbol)
    , (injSymbol subSort supSort, HeadType.Symbol)
    , (injSymbol unitSort supSort, HeadType.Symbol)
    , (injSymbol supSort supSort, HeadType.Symbol)
    , (pairSymbol unitSort, HeadType.Symbol)
    , (pairSymbol intSort, HeadType.Symbol)
    , (funSymbol, HeadType.Symbol)
    ]

tools :: SmtMetadataTools StepperAttributes
tools =
    Mock.makeMetadataTools
        symbolOrAliasAttrs
        symbolOrAliasType
        []
        []
        []
        Mock.emptySmtDeclarations

assertValue :: GHC.HasCallStack => TermLike Variable -> Assertion
assertValue termLike =
    assertEqual "Expected normalized pattern"
        concrete
        (concrete >>= roundTrip)
  where
    concrete = asConcrete termLike
    roundTrip patt = do
        value <- Value.fromConcreteStepPattern tools patt
        return (Value.asConcreteStepPattern value)

testValue :: GHC.HasCallStack => TestName -> TermLike Variable -> TestTree
testValue name = testCase name . assertValue

assertNotValue :: GHC.HasCallStack => TermLike Variable -> Assertion
assertNotValue purePattern =
    assertEqual "Unexpected normalized pattern"
        Nothing
        (concretePattern >>= Value.fromConcreteStepPattern tools)
  where
    concretePattern = asConcrete purePattern

testNotValue :: GHC.HasCallStack => TestName -> TermLike Variable -> TestTree
testNotValue name = testCase name . assertNotValue
