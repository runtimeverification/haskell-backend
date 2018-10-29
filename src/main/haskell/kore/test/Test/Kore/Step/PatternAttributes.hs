module Test.Kore.Step.PatternAttributes
    ( test_patternAttributes
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import Data.Reflection
       ( give )

import Kore.AST.Common
       ( BuiltinDomain (..), CharLiteral (..), CommonPurePattern,
       DomainValue (..), Sort (..), SortActual (..), StringLiteral (..) )
import Kore.AST.MetaOrObject
import Kore.ASTUtils.SmartConstructors
       ( mkCharLiteral, mkOr, mkStringLiteral, mkVar )
import Kore.IndexedModule.MetadataTools
       ( MetadataTools, SymbolOrAliasSorts )
import Kore.Proof.Functional
import Kore.Step.PatternAttributes
import Kore.Step.PatternAttributesError
       ( FunctionError (..), FunctionalError (..) )
import Kore.Step.StepperAttributes
       ( StepperAttributes )


import           Test.Kore
                 ( testId )
import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools, makeSymbolOrAliasSorts )
import qualified Test.Kore.Step.MockSymbols as MockSymbols
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

newtype LevelInt level = LevelInt Int
newtype LevelString level = LevelString String
    deriving (Show, Eq)

levelShow :: LevelInt level -> LevelString level
levelShow (LevelInt i) = LevelString (show i)

test_patternAttributes :: [TestTree]
test_patternAttributes = give mockSymbolOrAliasSorts
    [ testCase "variable mapping"
        (do
            assertEqualWithExplanation "FunctionalVariable"
                (FunctionalVariable (LevelString "10"))
                (mapFunctionalProofVariables
                    levelShow
                    (FunctionalVariable (LevelInt 10))
                )
            let
                dv = DomainValue
                    { domainValueSort = testSort
                    , domainValueChild =
                        BuiltinDomainPattern (mkStringLiteral "10")
                    }
            assertEqualWithExplanation "FunctionalDomainValue"
                (FunctionalDomainValue dv)
                (mapFunctionalProofVariables
                    levelShow
                    (FunctionalDomainValue dv)
                )
            assertEqualWithExplanation "FunctionalHead"
                (FunctionalHead MockSymbols.aSymbol)
                (mapFunctionalProofVariables
                    levelShow
                    (FunctionalHead MockSymbols.aSymbol)
                )
            assertEqualWithExplanation "FunctionalStringLiteral"
                (FunctionalStringLiteral (StringLiteral "10"))
                (mapFunctionalProofVariables
                    levelShow
                    (FunctionalStringLiteral (StringLiteral "10"))
                )
            assertEqualWithExplanation "FunctionalCharLiteral"
                (FunctionalCharLiteral (CharLiteral 'a'))
                (mapFunctionalProofVariables
                    levelShow
                    (FunctionalCharLiteral (CharLiteral 'a'))
                )
        )
    , testCase "isFunctionalPattern"
        (do
            assertEqualWithExplanation "variables are functional"
                (Right [FunctionalVariable Mock.x])
                (isFunctionalPattern
                    mockMetadataTools
                    (mkVar Mock.x)
                )
            let
                functionalConstant :: CommonPurePattern Object
                functionalConstant = Mock.functional00
            assertEqualWithExplanation "functional symbols are functional"
                (Right [FunctionalHead Mock.functional00Symbol])
                (isFunctionalPattern
                    mockMetadataTools
                    functionalConstant
                )
            let
                str :: CommonPurePattern Meta
                str = mkStringLiteral "10"
            assertEqualWithExplanation "string literals are functional"
                (Right [FunctionalStringLiteral (StringLiteral "10")])
                (isFunctionalPattern
                    mockMetaMetadataTools
                    str
                )
            let
                chr :: CommonPurePattern Meta
                chr = mkCharLiteral 'a'
            assertEqualWithExplanation "char literals are functional"
                (Right [FunctionalCharLiteral (CharLiteral 'a')])
                (isFunctionalPattern
                    mockMetaMetadataTools
                    chr
                )
            let
                functionConstant :: CommonPurePattern Object
                functionConstant = Mock.cf
            assertEqualWithExplanation "function symbols are not functional"
                (Left (NonFunctionalHead Mock.cfSymbol))
                (isFunctionalPattern
                    mockMetadataTools
                    functionConstant
                )
            let
                plainConstant :: CommonPurePattern Object
                plainConstant = Mock.plain00
            assertEqualWithExplanation "plain symbols are not functional"
                (Left (NonFunctionalHead Mock.plain00Symbol))
                (isFunctionalPattern
                    mockMetadataTools
                    plainConstant
                )
            let
                functionalPatt :: CommonPurePattern Object
                functionalPatt = Mock.functional10 Mock.a
            assertEqualWithExplanation "functional composition is functional"
                (Right
                    [ FunctionalHead Mock.functional10Symbol
                    , FunctionalHead Mock.aSymbol
                    ]
                )
                (isFunctionalPattern
                    mockMetadataTools
                    functionalPatt
                )
            let
                nonFunctionalPatt :: CommonPurePattern Object
                nonFunctionalPatt =
                    mkOr Mock.a Mock.b
            assertEqualWithExplanation "or is not functional"
                (Left NonFunctionalPattern)
                (isFunctionalPattern
                    mockMetadataTools
                    nonFunctionalPatt
                )
        )
    , testCase "isFunctionPattern"
        (do
            assertEqualWithExplanation "variables are function-like"
                (Right [FunctionProofFunctional (FunctionalVariable Mock.x)])
                (isFunctionPattern
                    mockMetadataTools
                    (mkVar Mock.x)
                )
            let
                functionalConstant :: CommonPurePattern Object
                functionalConstant = Mock.functional00
            assertEqualWithExplanation "functional symbols are function-like"
                (Right
                    [ FunctionProofFunctional
                        (FunctionalHead Mock.functional00Symbol)
                    ]
                )
                (isFunctionPattern
                    mockMetadataTools
                    functionalConstant
                )
            let
                str :: CommonPurePattern Meta
                str = mkStringLiteral "10"
            assertEqualWithExplanation "string literals are function-like"
                (Right
                    [ FunctionProofFunctional
                        (FunctionalStringLiteral (StringLiteral "10"))
                    ]
                )
                (isFunctionPattern
                    mockMetaMetadataTools
                    str
                )
            let
                chr :: CommonPurePattern Meta
                chr = mkCharLiteral 'a'
            assertEqualWithExplanation "char literals are function-like"
                (Right
                    [ FunctionProofFunctional
                        (FunctionalCharLiteral (CharLiteral 'a'))
                    ]
                )
                (isFunctionPattern
                    mockMetaMetadataTools
                    chr
                )
            let
                functionConstant :: CommonPurePattern Object
                functionConstant = Mock.cf
            assertEqualWithExplanation "function symbols are function-like"
                (Right [FunctionHead Mock.cfSymbol])
                (isFunctionPattern
                    mockMetadataTools
                    functionConstant
                )
            let
                plainConstant :: CommonPurePattern Object
                plainConstant = Mock.plain00
            assertEqualWithExplanation "plain symbols are not function-like"
                (Left (NonFunctionHead Mock.plain00Symbol))
                (isFunctionPattern
                    mockMetadataTools
                    plainConstant
                )
            let
                functionalPatt :: CommonPurePattern Object
                functionalPatt = Mock.functional10 Mock.a
            assertEqualWithExplanation "functional composition is function-like"
                (Right
                    [ FunctionProofFunctional
                        (FunctionalHead Mock.functional10Symbol)
                    , FunctionProofFunctional
                        (FunctionalHead Mock.aSymbol)
                    ]
                )
                (isFunctionPattern
                    mockMetadataTools
                    functionalPatt
                )
            let
                nonFunctionPatt :: CommonPurePattern Object
                nonFunctionPatt =
                    mkOr Mock.a Mock.a
            assertEqualWithExplanation "or is not function-like"
                (Left NonFunctionPattern)
                (isFunctionPattern
                    mockMetadataTools
                    nonFunctionPatt
                )
        )
    ]
  where
    mockSymbolOrAliasSorts :: SymbolOrAliasSorts Object
    mockSymbolOrAliasSorts =
        Mock.makeSymbolOrAliasSorts Mock.symbolOrAliasSortsMapping
    mockMetadataTools :: MetadataTools Object StepperAttributes
    mockMetadataTools =
        Mock.makeMetadataTools
            mockSymbolOrAliasSorts
            Mock.attributesMapping
            Mock.headTypeMapping
            Mock.subsorts

    mockMetaSymbolOrAliasSorts :: SymbolOrAliasSorts Meta
    mockMetaSymbolOrAliasSorts = Mock.makeSymbolOrAliasSorts []
    mockMetaMetadataTools :: MetadataTools Meta StepperAttributes
    mockMetaMetadataTools =
        Mock.makeMetadataTools mockMetaSymbolOrAliasSorts [] [] []

testSort :: Sort Object
testSort =
    SortActualSort SortActual
        { sortActualName  = testId "testSort"
        , sortActualSorts = []
        }
