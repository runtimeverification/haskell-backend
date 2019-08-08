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
       ( ConstructorLikeError (..) )

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
    , testCase "isConstructorLikePattern"
        (do
            assertEqualWithExplanation "variables are constructor-like"
                (Right [ConstructorLikeProof])
                (isConstructorLikePattern
                    Mock.metadataTools
                    (mkElemVar Mock.x)
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
                sortInjection = Mock.sortInjection10 Mock.aSort0
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
                    (mkElemVar Mock.x)
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
                sortInjection = Mock.sortInjection10 Mock.aSort0
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
