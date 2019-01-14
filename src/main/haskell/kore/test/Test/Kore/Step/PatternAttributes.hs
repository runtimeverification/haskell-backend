module Test.Kore.Step.PatternAttributes
    ( test_patternAttributes
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Kore.AST.Pure
import           Kore.AST.Valid
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Proof.Functional
import           Kore.Step.Pattern
import           Kore.Step.PatternAttributes
import           Kore.Step.PatternAttributesError
                 ( ConstructorLikeError (..), FunctionError (..),
                 FunctionalError (..) )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )

import           Test.Kore
                 ( testId )
import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeMetadataTools )
import qualified Test.Kore.Step.MockSymbols as MockSymbols
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

newtype LevelInt level = LevelInt Int
newtype LevelString level = LevelString String
    deriving (Show, Eq)

levelShow :: LevelInt level -> LevelString level
levelShow (LevelInt i) = LevelString (show i)

test_patternAttributes :: [TestTree]
test_patternAttributes =
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
                        Domain.BuiltinPattern
                        $ eraseAnnotations
                        $ mkStringLiteral "10"
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
                functionalConstant :: CommonStepPattern Object
                functionalConstant = Mock.functional00
            assertEqualWithExplanation "functional symbols are functional"
                (Right [FunctionalHead Mock.functional00Symbol])
                (isFunctionalPattern
                    mockMetadataTools
                    functionalConstant
                )
            let
                str :: CommonStepPattern Meta
                str = mkStringLiteral "10"
            assertEqualWithExplanation "string literals are functional"
                (Right [FunctionalStringLiteral (StringLiteral "10")])
                (isFunctionalPattern
                    mockMetaMetadataTools
                    str
                )
            let
                chr :: CommonStepPattern Meta
                chr = mkCharLiteral 'a'
            assertEqualWithExplanation "char literals are functional"
                (Right [FunctionalCharLiteral (CharLiteral 'a')])
                (isFunctionalPattern
                    mockMetaMetadataTools
                    chr
                )
            let
                functionConstant :: CommonStepPattern Object
                functionConstant = Mock.cf
            assertEqualWithExplanation "function symbols are not functional"
                (Left (NonFunctionalHead Mock.cfSymbol))
                (isFunctionalPattern
                    mockMetadataTools
                    functionConstant
                )
            let
                plainConstant :: CommonStepPattern Object
                plainConstant = Mock.plain00
            assertEqualWithExplanation "plain symbols are not functional"
                (Left (NonFunctionalHead Mock.plain00Symbol))
                (isFunctionalPattern
                    mockMetadataTools
                    plainConstant
                )
            let
                functionalPatt :: CommonStepPattern Object
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
                nonFunctionalPatt :: CommonStepPattern Object
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
                functionalConstant :: CommonStepPattern Object
                functionalConstant = Mock.functional00
            assertEqualWithExplanation "functional symbols are function-like"
                (Right
                    [ FunctionHead Mock.functional00Symbol
                    ]
                )
                (isFunctionPattern
                    mockMetadataTools
                    functionalConstant
                )
            let
                str :: CommonStepPattern Meta
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
                chr :: CommonStepPattern Meta
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
                functionConstant :: CommonStepPattern Object
                functionConstant = Mock.cf
            assertEqualWithExplanation "function symbols are function-like"
                (Right [FunctionHead Mock.cfSymbol])
                (isFunctionPattern
                    mockMetadataTools
                    functionConstant
                )
            let
                plainConstant :: CommonStepPattern Object
                plainConstant = Mock.plain00
            assertEqualWithExplanation "plain symbols are not function-like"
                (Left (NonFunctionHead Mock.plain00Symbol))
                (isFunctionPattern
                    mockMetadataTools
                    plainConstant
                )
            let
                functionalPatt :: CommonStepPattern Object
                functionalPatt = Mock.functional10 Mock.a
            assertEqualWithExplanation "functional composition is function-like"
                (Right
                    [ FunctionHead Mock.functional10Symbol
                    , FunctionHead Mock.aSymbol
                    ]
                )
                (isFunctionPattern
                    mockMetadataTools
                    functionalPatt
                )
            let
                nonFunctionPatt :: CommonStepPattern Object
                nonFunctionPatt =
                    mkOr Mock.a Mock.a
            assertEqualWithExplanation "or is not function-like"
                (Left NonFunctionPattern)
                (isFunctionPattern
                    mockMetadataTools
                    nonFunctionPatt
                )
        )
    , testCase "isConstructorLikePattern"
        (do
            assertEqualWithExplanation "variables are constructor-like"
                (Right [ConstructorLikeProof])
                (isConstructorLikePattern
                    mockMetadataTools
                    (mkVar Mock.x)
                )
            let
                constructor :: CommonStepPattern Object
                constructor = Mock.a
            assertEqualWithExplanation "constructors are constructor-like"
                (Right [ConstructorLikeProof])
                (isConstructorLikePattern
                    mockMetadataTools
                    constructor
                )
            let
                sortInjection :: CommonStepPattern Object
                sortInjection = Mock.sortInjection10 Mock.a
            assertEqualWithExplanation "sort injections are constructor-like"
                (Right [ConstructorLikeProof, ConstructorLikeProof])
                (isConstructorLikePattern
                    mockMetadataTools
                    sortInjection
                )
            let
                mapElement :: CommonStepPattern Object
                mapElement = Mock.elementMap Mock.a Mock.b
            assertEqualWithExplanation
                "constructors-modulo are not constructor-like"
                (Left NonConstructorLikeHead)
                (isConstructorLikePattern
                    mockMetadataTools
                    mapElement
                )
            let
                str :: CommonStepPattern Meta
                str = mkStringLiteral "10"
            assertEqualWithExplanation "string literals are constructor-like"
                (Right [ConstructorLikeProof])
                (isConstructorLikePattern
                    mockMetaMetadataTools
                    str
                )
            let
                chr :: CommonStepPattern Meta
                chr = mkCharLiteral 'a'
            assertEqualWithExplanation "char literals are constructor-like"
                (Right [ConstructorLikeProof])
                (isConstructorLikePattern
                    mockMetaMetadataTools
                    chr
                )
            let
                dv :: CommonStepPattern Object
                dv = mkDomainValue
                        Mock.testSort
                        (Domain.BuiltinPattern
                            $ eraseAnnotations
                            $ mkStringLiteral "a"
                        )
            assertEqualWithExplanation "domain values are constructor-like"
                (Right [ConstructorLikeProof])
                (isConstructorLikePattern
                    mockMetadataTools
                    dv
                )

            let
                functionConstant :: CommonStepPattern Object
                functionConstant = Mock.cf
            assertEqualWithExplanation
                "function symbols are not constructor-like"
                (Left NonConstructorLikeHead)
                (isConstructorLikePattern
                    mockMetadataTools
                    functionConstant
                )
            let
                injectionConstant :: CommonStepPattern Object
                injectionConstant = Mock.injective10 Mock.a
            assertEqualWithExplanation "injections are not constructor-like"
                (Left NonConstructorLikeHead)
                (isConstructorLikePattern
                    mockMetadataTools
                    injectionConstant
                )
        )
    , testCase "isConstructorModuloLikePattern"
        (do
            assertEqualWithExplanation "variables are constructor-modulo-like"
                (Right [ConstructorLikeProof])
                (isConstructorModuloLikePattern
                    mockMetadataTools
                    (mkVar Mock.x)
                )
            let
                constructor :: CommonStepPattern Object
                constructor = Mock.a
            assertEqualWithExplanation
                "constructors are constructor-modulo-like"
                (Right [ConstructorLikeProof])
                (isConstructorModuloLikePattern
                    mockMetadataTools
                    constructor
                )
            let
                sortInjection :: CommonStepPattern Object
                sortInjection = Mock.sortInjection10 Mock.a
            assertEqualWithExplanation
                "sort injections are constructor-modulo-like"
                (Right [ConstructorLikeProof, ConstructorLikeProof])
                (isConstructorModuloLikePattern
                    mockMetadataTools
                    sortInjection
                )
            let
                mapElement :: CommonStepPattern Object
                mapElement = Mock.elementMap Mock.a Mock.b
            assertEqualWithExplanation
                "constructors-modulo are constructor-modulo-like"
                (Right
                    [ ConstructorLikeProof
                    , ConstructorLikeProof
                    , ConstructorLikeProof
                    ]
                )
                (isConstructorModuloLikePattern
                    mockMetadataTools
                    mapElement
                )
            let
                str :: CommonStepPattern Meta
                str = mkStringLiteral "10"
            assertEqualWithExplanation
                "string literals are constructor-modulo-like"
                (Right [ConstructorLikeProof])
                (isConstructorModuloLikePattern
                    mockMetaMetadataTools
                    str
                )
            let
                chr :: CommonStepPattern Meta
                chr = mkCharLiteral 'a'
            assertEqualWithExplanation
                "char literals are constructor-modulo-like"
                (Right [ConstructorLikeProof])
                (isConstructorModuloLikePattern
                    mockMetaMetadataTools
                    chr
                )
            let
                dv :: CommonStepPattern Object
                dv = mkDomainValue
                        Mock.testSort
                        (Domain.BuiltinPattern
                            $ eraseAnnotations
                            $ mkStringLiteral "a"
                        )
            assertEqualWithExplanation
                "domain values are constructor-modulo-like"
                (Right [ConstructorLikeProof])
                (isConstructorModuloLikePattern
                    mockMetadataTools
                    dv
                )

            let
                functionConstant :: CommonStepPattern Object
                functionConstant = Mock.cf
            assertEqualWithExplanation
                "function symbols are not constructor-modulo-like"
                (Left NonConstructorLikeHead)
                (isConstructorModuloLikePattern
                    mockMetadataTools
                    functionConstant
                )
            let
                injectionConstant :: CommonStepPattern Object
                injectionConstant = Mock.injective10 Mock.a
            assertEqualWithExplanation
                "injections are not constructor-modulo-like"
                (Left NonConstructorLikeHead)
                (isConstructorModuloLikePattern
                    mockMetadataTools
                    injectionConstant
                )
        )
    ]
  where
    mockMetadataTools :: MetadataTools Object StepperAttributes
    mockMetadataTools =
        Mock.makeMetadataTools
            Mock.attributesMapping
            Mock.headTypeMapping
            Mock.sortAttributesMapping
            Mock.subsorts

    mockMetaMetadataTools :: MetadataTools Meta StepperAttributes
    mockMetaMetadataTools = Mock.makeMetadataTools [] [] [] []

testSort :: Sort Object
testSort =
    SortActualSort SortActual
        { sortActualName  = testId "testSort"
        , sortActualSorts = []
        }
