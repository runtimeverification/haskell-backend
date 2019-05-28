module Test.Kore.Step.PatternAttributes
    ( test_patternAttributes
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import Kore.Internal.TermLike
import Kore.Proof.Functional as Proof.Functional
import Kore.Step.PatternAttributes
import Kore.Step.PatternAttributesError
       ( ConstructorLikeError (..), FunctionError (..), FunctionalError (..) )

import           Test.Kore.Comparators ()
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
                (Proof.Functional.mapVariables
                    levelShow
                    (FunctionalVariable (LevelInt 10))
                )
            assertEqualWithExplanation "FunctionalHead"
                (FunctionalHead MockSymbols.aSymbol)
                (Proof.Functional.mapVariables
                    levelShow
                    (FunctionalHead MockSymbols.aSymbol)
                )
            assertEqualWithExplanation "FunctionalStringLiteral"
                (FunctionalStringLiteral (StringLiteral "10"))
                (Proof.Functional.mapVariables
                    levelShow
                    (FunctionalStringLiteral (StringLiteral "10"))
                )
            assertEqualWithExplanation "FunctionalCharLiteral"
                (FunctionalCharLiteral (CharLiteral 'a'))
                (Proof.Functional.mapVariables
                    levelShow
                    (FunctionalCharLiteral (CharLiteral 'a'))
                )
        )
    , testCase "isFunctionalPattern"
        (do
            assertEqualWithExplanation "variables are functional"
                (Right [FunctionalVariable Mock.x])
                (isFunctionalPattern
                    Mock.metadataTools
                    (mkVar Mock.x)
                )
            let
                functionalConstant :: TermLike Variable
                functionalConstant = Mock.functional00
            assertEqualWithExplanation "functional symbols are functional"
                (Right [FunctionalHead Mock.functional00Symbol])
                (isFunctionalPattern
                    Mock.metadataTools
                    functionalConstant
                )
            let
                str :: TermLike Variable
                str = mkStringLiteral "10"
            assertEqualWithExplanation "string literals are functional"
                (Right [FunctionalStringLiteral (StringLiteral "10")])
                (isFunctionalPattern
                    Mock.metadataTools
                    str
                )
            let
                chr :: TermLike Variable
                chr = mkCharLiteral 'a'
            assertEqualWithExplanation "char literals are functional"
                (Right [FunctionalCharLiteral (CharLiteral 'a')])
                (isFunctionalPattern
                    Mock.metadataTools
                    chr
                )
            let
                functionConstant :: TermLike Variable
                functionConstant = Mock.cf
            assertEqualWithExplanation "function symbols are not functional"
                (Left (NonFunctionalHead Mock.cfSymbol))
                (isFunctionalPattern
                    Mock.metadataTools
                    functionConstant
                )
            let
                plainConstant :: TermLike Variable
                plainConstant = Mock.plain00
            assertEqualWithExplanation "plain symbols are not functional"
                (Left (NonFunctionalHead Mock.plain00Symbol))
                (isFunctionalPattern
                    Mock.metadataTools
                    plainConstant
                )
            let
                functionalPatt :: TermLike Variable
                functionalPatt = Mock.functional10 Mock.a
            assertEqualWithExplanation "functional composition is functional"
                (Right
                    [ FunctionalHead Mock.functional10Symbol
                    , FunctionalHead Mock.aSymbol
                    ]
                )
                (isFunctionalPattern
                    Mock.metadataTools
                    functionalPatt
                )
            let
                nonFunctionalPatt :: TermLike Variable
                nonFunctionalPatt =
                    mkOr Mock.a Mock.b
            assertEqualWithExplanation "or is not functional"
                (Left NonFunctionalPattern)
                (isFunctionalPattern
                    Mock.metadataTools
                    nonFunctionalPatt
                )
        )
    , testCase "isFunctionPattern"
        (do
            assertEqualWithExplanation "variables are function-like"
                (Right [FunctionProofFunctional (FunctionalVariable Mock.x)])
                (isFunctionPattern
                    Mock.metadataTools
                    (mkVar Mock.x)
                )
            let
                functionalConstant :: TermLike Variable
                functionalConstant = Mock.functional00
            assertEqualWithExplanation "functional symbols are function-like"
                (Right
                    [ FunctionHead Mock.functional00Symbol
                    ]
                )
                (isFunctionPattern
                    Mock.metadataTools
                    functionalConstant
                )
            let
                str :: TermLike Variable
                str = mkStringLiteral "10"
            assertEqualWithExplanation "string literals are function-like"
                (Right
                    [ FunctionProofFunctional
                        (FunctionalStringLiteral (StringLiteral "10"))
                    ]
                )
                (isFunctionPattern
                    Mock.metadataTools
                    str
                )
            let
                chr :: TermLike Variable
                chr = mkCharLiteral 'a'
            assertEqualWithExplanation "char literals are function-like"
                (Right
                    [ FunctionProofFunctional
                        (FunctionalCharLiteral (CharLiteral 'a'))
                    ]
                )
                (isFunctionPattern
                    Mock.metadataTools
                    chr
                )
            let
                functionConstant :: TermLike Variable
                functionConstant = Mock.cf
            assertEqualWithExplanation "function symbols are function-like"
                (Right [FunctionHead Mock.cfSymbol])
                (isFunctionPattern
                    Mock.metadataTools
                    functionConstant
                )
            let
                plainConstant :: TermLike Variable
                plainConstant = Mock.plain00
            assertEqualWithExplanation "plain symbols are not function-like"
                (Left (NonFunctionHead Mock.plain00Symbol))
                (isFunctionPattern
                    Mock.metadataTools
                    plainConstant
                )
            let
                functionalPatt :: TermLike Variable
                functionalPatt = Mock.functional10 Mock.a
            assertEqualWithExplanation "functional composition is function-like"
                (Right
                    [ FunctionHead Mock.functional10Symbol
                    , FunctionHead Mock.aSymbol
                    ]
                )
                (isFunctionPattern
                    Mock.metadataTools
                    functionalPatt
                )
            let
                nonFunctionPatt :: TermLike Variable
                nonFunctionPatt =
                    mkOr Mock.a Mock.a
            assertEqualWithExplanation "or is not function-like"
                (Left NonFunctionPattern)
                (isFunctionPattern
                    Mock.metadataTools
                    nonFunctionPatt
                )
        )
    , testCase "isConstructorLikePattern"
        (do
            assertEqualWithExplanation "variables are constructor-like"
                (Right [ConstructorLikeProof])
                (isConstructorLikePattern
                    Mock.metadataTools
                    (mkVar Mock.x)
                )
            let
                constructor :: TermLike Variable
                constructor = Mock.a
            assertEqualWithExplanation "constructors are constructor-like"
                (Right [ConstructorLikeProof])
                (isConstructorLikePattern
                    Mock.metadataTools
                    constructor
                )
            let
                sortInjection :: TermLike Variable
                sortInjection = Mock.sortInjection10 Mock.a
            assertEqualWithExplanation "sort injections are constructor-like"
                (Right [ConstructorLikeProof, ConstructorLikeProof])
                (isConstructorLikePattern
                    Mock.metadataTools
                    sortInjection
                )
            let
                mapElement :: TermLike Variable
                mapElement = Mock.elementMap Mock.a Mock.b
            assertEqualWithExplanation
                "constructors-modulo are not constructor-like"
                (Left NonConstructorLikeHead)
                (isConstructorLikePattern
                    Mock.metadataTools
                    mapElement
                )
            let
                str :: TermLike Variable
                str = mkStringLiteral "10"
            assertEqualWithExplanation "string literals are constructor-like"
                (Right [ConstructorLikeProof])
                (isConstructorLikePattern
                    Mock.metadataTools
                    str
                )
            let
                chr :: TermLike Variable
                chr = mkCharLiteral 'a'
            assertEqualWithExplanation "char literals are constructor-like"
                (Right [ConstructorLikeProof])
                (isConstructorLikePattern
                    Mock.metadataTools
                    chr
                )
            let
                dv :: TermLike Variable
                dv =
                    mkDomainValue DomainValue
                        { domainValueSort = Mock.testSort
                        , domainValueChild = mkStringLiteral "a"
                        }
            assertEqualWithExplanation "domain values are constructor-like"
                (Right [ConstructorLikeProof])
                (isConstructorLikePattern
                    Mock.metadataTools
                    dv
                )

            let
                functionConstant :: TermLike Variable
                functionConstant = Mock.cf
            assertEqualWithExplanation
                "function symbols are not constructor-like"
                (Left NonConstructorLikeHead)
                (isConstructorLikePattern
                    Mock.metadataTools
                    functionConstant
                )
            let
                injectionConstant :: TermLike Variable
                injectionConstant = Mock.injective10 Mock.a
            assertEqualWithExplanation "injections are not constructor-like"
                (Left NonConstructorLikeHead)
                (isConstructorLikePattern
                    Mock.metadataTools
                    injectionConstant
                )
        )
    , testCase "isConstructorModuloLikePattern"
        (do
            assertEqualWithExplanation "variables are constructor-modulo-like"
                (Right [ConstructorLikeProof])
                (isConstructorModuloLikePattern
                    Mock.metadataTools
                    (mkVar Mock.x)
                )
            let
                constructor :: TermLike Variable
                constructor = Mock.a
            assertEqualWithExplanation
                "constructors are constructor-modulo-like"
                (Right [ConstructorLikeProof])
                (isConstructorModuloLikePattern
                    Mock.metadataTools
                    constructor
                )
            let
                sortInjection :: TermLike Variable
                sortInjection = Mock.sortInjection10 Mock.a
            assertEqualWithExplanation
                "sort injections are constructor-modulo-like"
                (Right [ConstructorLikeProof, ConstructorLikeProof])
                (isConstructorModuloLikePattern
                    Mock.metadataTools
                    sortInjection
                )
            let
                mapElement :: TermLike Variable
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
                    Mock.metadataTools
                    mapElement
                )
            let
                str :: TermLike Variable
                str = mkStringLiteral "10"
            assertEqualWithExplanation
                "string literals are constructor-modulo-like"
                (Right [ConstructorLikeProof])
                (isConstructorModuloLikePattern
                    Mock.metadataTools
                    str
                )
            let
                chr :: TermLike Variable
                chr = mkCharLiteral 'a'
            assertEqualWithExplanation
                "char literals are constructor-modulo-like"
                (Right [ConstructorLikeProof])
                (isConstructorModuloLikePattern
                    Mock.metadataTools
                    chr
                )
            let
                dv :: TermLike Variable
                dv =
                    mkDomainValue DomainValue
                        { domainValueSort = Mock.testSort
                        , domainValueChild = mkStringLiteral "a"
                        }
            assertEqualWithExplanation
                "domain values are constructor-modulo-like"
                (Right [ConstructorLikeProof])
                (isConstructorModuloLikePattern
                    Mock.metadataTools
                    dv
                )

            let
                functionConstant :: TermLike Variable
                functionConstant = Mock.cf
            assertEqualWithExplanation
                "function symbols are not constructor-modulo-like"
                (Left NonConstructorLikeHead)
                (isConstructorModuloLikePattern
                    Mock.metadataTools
                    functionConstant
                )
            let
                injectionConstant :: TermLike Variable
                injectionConstant = Mock.injective10 Mock.a
            assertEqualWithExplanation
                "injections are not constructor-modulo-like"
                (Left NonConstructorLikeHead)
                (isConstructorModuloLikePattern
                    Mock.metadataTools
                    injectionConstant
                )
        )
    ]
