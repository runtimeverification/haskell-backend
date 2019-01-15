module Test.Kore.Proof.Value where

import Test.Tasty
import Test.Tasty.HUnit

import           Kore.AST.Pure
import           Kore.AST.Valid
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( HeadType, MetadataTools )
import qualified Kore.IndexedModule.MetadataTools as HeadType
                 ( HeadType (..) )
import qualified Kore.Proof.Value as Value
import           Kore.Step.Pattern
import           Kore.Step.StepperAttributes

import           Test.Kore
import           Test.Kore.Builtin.Definition
                 ( intSort )
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock

unit_constructorUnit :: Assertion
unit_constructorUnit = assertValue unitPattern

unit_domainValue :: Assertion
unit_domainValue = assertValue onePattern

unit_injConstructor :: Assertion
unit_injConstructor = assertValue (mkInj unitPattern)

unit_injInj :: Assertion
unit_injInj = assertNotValue (mkInj (mkInj unitPattern))

unit_pairConstructor :: Assertion
unit_pairConstructor = assertValue (mkPair unitPattern unitPattern)

test_pairDomainValue :: [TestTree]
test_pairDomainValue =
    [ testValue "(0, 0)" (mkPair zeroPattern zeroPattern)
    , testValue "(0, 1)" (mkPair zeroPattern onePattern)
    , testValue "(1, 1)" (mkPair onePattern onePattern)
    , testValue "(1, 0)" (mkPair onePattern zeroPattern)
    ]

unit_fun :: Assertion
unit_fun =
    assertNotValue (mkApp intSort funSymbol [onePattern])

mkInj :: CommonStepPattern Object -> CommonStepPattern Object
mkInj input =
    mkApp supSort (injSymbol (getSort input) supSort) [input]

mkPair
    :: CommonStepPattern Object
    -> CommonStepPattern Object
    -> CommonStepPattern Object
mkPair a b =
    mkApp (pairSort inputSort') (pairSymbol inputSort') [a, b]
  where
    inputSort' = getSort a

unitPattern :: CommonStepPattern Object
unitPattern = mkApp unitSort unitSymbol []

onePattern :: CommonStepPattern Object
onePattern =
    (mkDomainValue intSort . Domain.BuiltinPattern . eraseAnnotations)
        (mkStringLiteral "1")

zeroPattern :: CommonStepPattern Object
zeroPattern =
    (mkDomainValue intSort . Domain.BuiltinPattern . eraseAnnotations)
        (mkStringLiteral "1")

unitSort :: Sort Object
unitSort =
    SortActualSort SortActual
        { sortActualName = testId "Unit"
        , sortActualSorts = []
        }

unitSymbol :: SymbolOrAlias Object
unitSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = testId "unit"
        , symbolOrAliasParams = []
        }

pairSort :: Sort Object -> Sort Object
pairSort sort =
    SortActualSort SortActual
        { sortActualName = testId "Pair"
        , sortActualSorts = [sort]
        }

pairSymbol :: Sort Object -> SymbolOrAlias Object
pairSymbol sort =
    SymbolOrAlias
        { symbolOrAliasConstructor = testId "pair"
        , symbolOrAliasParams = [sort]
        }

injSymbol :: Sort Object -> Sort Object -> SymbolOrAlias Object
injSymbol sub sup =
    SymbolOrAlias
        { symbolOrAliasConstructor = testId "inj"
        , symbolOrAliasParams = [sub, sup]
        }

funSymbol :: SymbolOrAlias Object
funSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = testId "fun"
        , symbolOrAliasParams = []
        }

subSort :: Sort level
subSort = (SortVariableSort . SortVariable) (testId "sub")

supSort :: Sort level
supSort = (SortVariableSort . SortVariable) (testId "sup")

symbolOrAliasAttrs :: [(SymbolOrAlias Object, StepperAttributes)]
symbolOrAliasAttrs =
    [ (unitSymbol, Mock.constructorAttributes)
    , (injSymbol subSort supSort, Mock.sortInjectionAttributes)
    , (injSymbol unitSort supSort, Mock.sortInjectionAttributes)
    , (injSymbol supSort supSort, Mock.sortInjectionAttributes)
    , (pairSymbol unitSort, Mock.constructorAttributes)
    , (pairSymbol intSort, Mock.constructorAttributes)
    , (funSymbol, Mock.functionAttributes)
    ]

symbolOrAliasType :: [(SymbolOrAlias Object, HeadType)]
symbolOrAliasType =
    [ (unitSymbol, HeadType.Symbol)
    , (injSymbol subSort supSort, HeadType.Symbol)
    , (injSymbol unitSort supSort, HeadType.Symbol)
    , (injSymbol supSort supSort, HeadType.Symbol)
    , (pairSymbol unitSort, HeadType.Symbol)
    , (pairSymbol intSort, HeadType.Symbol)
    , (funSymbol, HeadType.Symbol)
    ]

tools :: MetadataTools Object StepperAttributes
tools =
    Mock.makeMetadataTools
        symbolOrAliasAttrs
        symbolOrAliasType
        []
        []

assertValue :: CommonStepPattern Object -> Assertion
assertValue purePattern =
    assertEqual "Expected normalized pattern"
        concretePattern
        (concretePattern >>= roundTrip)
  where
    concretePattern = asConcreteStepPattern purePattern
    roundTrip patt = do
        value <- Value.fromConcreteStepPattern tools patt
        return (Value.asConcreteStepPattern value)

testValue :: TestName -> CommonStepPattern Object -> TestTree
testValue name = testCase name . assertValue

assertNotValue :: CommonStepPattern Object -> Assertion
assertNotValue purePattern =
    assertEqual "Unexpected normalized pattern"
        Nothing
        (concretePattern >>= Value.fromConcreteStepPattern tools)
  where
    concretePattern = asConcreteStepPattern purePattern
