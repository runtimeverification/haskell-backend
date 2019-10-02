module Test.Kore.Step.PatternAttributes
    ( test_patternAttributes
    ) where

import Test.Tasty

import Data.Functor.Const

import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Domain.Builtin
import Kore.Internal.TermLike
import Kore.Proof.Functional as Proof.Functional
import Kore.Step.PatternAttributes
import Kore.Step.PatternAttributesError
    ( ConstructorLikeError (..)
    )

import qualified Test.Kore.Step.MockSymbols as MockSymbols
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty.HUnit.Ext

newtype LevelInt level = LevelInt Int
newtype LevelString level = LevelString String
    deriving (Eq, GHC.Generic, Show)

instance SOP.Generic (LevelString level)

instance SOP.HasDatatypeInfo (LevelString level)

instance Debug (LevelString level)

instance Diff (LevelString level)

levelShow :: LevelInt level -> LevelString level
levelShow (LevelInt i) = LevelString (show i)

test_patternAttributes :: [TestTree]
test_patternAttributes =
    [ testCase "patternattributes variable mapping"
        (do
            assertEqual "FunctionalVariable"
                (FunctionalVariable (LevelString "10"))
                (Proof.Functional.mapVariables
                    levelShow
                    (FunctionalVariable (LevelInt 10))
                )
            assertEqual "FunctionalHead"
                (FunctionalHead MockSymbols.aSymbol)
                (Proof.Functional.mapVariables
                    levelShow
                    (FunctionalHead MockSymbols.aSymbol)
                )
            assertEqual "FunctionalStringLiteral"
                (FunctionalStringLiteral (StringLiteral "10"))
                (Proof.Functional.mapVariables
                    levelShow
                    (FunctionalStringLiteral (StringLiteral "10"))
                )
            assertEqual "FunctionalCharLiteral"
                (FunctionalCharLiteral (CharLiteral 'a'))
                (Proof.Functional.mapVariables
                    levelShow
                    (FunctionalCharLiteral (CharLiteral 'a'))
                )
        )
    , testCase "patternattributes isConstructorLikePattern"
        (do
            assertEqual "variables are constructor-like"
                (Right [ConstructorLikeProof])
                (isConstructorLikePattern
                    Mock.metadataTools
                    (mkElemVar Mock.x)
                )
            let
                constructor :: TermLike Variable
                constructor = Mock.a
            assertEqual "constructors are constructor-like"
                (Right [ConstructorLikeProof])
                (isConstructorLikePattern
                    Mock.metadataTools
                    constructor
                )
            let
                sortInjection :: TermLike Variable
                sortInjection = Mock.sortInjection10 Mock.aSort0
            assertEqual "sort injections are constructor-like"
                (Right [ConstructorLikeProof, ConstructorLikeProof])
                (isConstructorLikePattern
                    Mock.metadataTools
                    sortInjection
                )
            let
                mapElement :: TermLike Variable
                mapElement = Mock.elementMap Mock.a Mock.b
            assertEqual
                "constructors-modulo are not constructor-like"
                (Left NonConstructorLikeHead)
                (isConstructorLikePattern
                    Mock.metadataTools
                    mapElement
                )
            let
                str :: TermLike Variable
                str = mkStringLiteral "10"
            assertEqual "string literals are constructor-like"
                (Right [ConstructorLikeProof])
                (isConstructorLikePattern
                    Mock.metadataTools
                    str
                )
            let
                chr :: TermLike Variable
                chr = mkCharLiteral 'a'
            assertEqual "char literals are constructor-like"
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
            assertEqual "domain values are constructor-like"
                (Right [ConstructorLikeProof])
                (isConstructorLikePattern
                    Mock.metadataTools
                    dv
                )

            let
                functionConstant :: TermLike Variable
                functionConstant = Mock.cf
            assertEqual
                "function symbols are not constructor-like"
                (Left NonConstructorLikeHead)
                (isConstructorLikePattern
                    Mock.metadataTools
                    functionConstant
                )
            let
                injectionConstant :: TermLike Variable
                injectionConstant = Mock.injective10 Mock.a
            assertEqual "injections are not constructor-like"
                (Left NonConstructorLikeHead)
                (isConstructorLikePattern
                    Mock.metadataTools
                    injectionConstant
                )
        )
    , testCase "patternattributes isConstructorLikeTop"
        (do
            assertEqual "ApplySymbolF is constructor-like-top"
                True
                (isConstructorLikeTop 
                    Mock.metadataTools
                    $ undefined :< 
                        (ApplySymbolF Application 
                            { applicationSymbolOrAlias = Mock.aSymbol
                            , applicationChildren = undefined
                            }
                        )
                )
            assertEqual "DomainValueF is constructor-like-top"
                True
                (isConstructorLikeTop
                    Mock.metadataTools
                    $ undefined :<
                        DomainValueF 
                            (DomainValue 
                                { domainValueSort = Mock.testSort
                                , domainValueChild = Mock.aSymbol
                                }
                            )

                )
            assertEqual "BuiltinF is constructor-like-top"
                True
                (isConstructorLikeTop
                    Mock.metadataTools
                    $ undefined :<
                        BuiltinF (BuiltinInt (InternalInt
                            { builtinIntSort = Mock.intSort
                            , builtinIntValue = 1 
                            }
                        ))
                )
            assertEqual "StringLiteralF is constructor-like-top"
                True
                (isConstructorLikeTop
                    Mock.metadataTools
                    $ undefined :<
                        StringLiteralF (
                            Const (
                                StringLiteral
                                    {
                                        getStringLiteral = mempty
                                    }
                            )
                        )
                )
            assertEqual "CharLiteralF is constructor-like-top"
                True
                (isConstructorLikeTop
                    Mock.metadataTools
                    $ undefined :<
                        CharLiteralF (
                            Const (
                                CharLiteral
                                    {
                                        getCharLiteral = 'a' 
                                    }
                            )
                        )
                )
            assertEqual "AndF is not is constructor-like-top"
                False
                (isConstructorLikeTop
                    Mock.metadataTools
                    $ undefined :<
                        AndF (
                           And 
                            { andSort = Mock.testSort
                            , andFirst = Mock.aSymbol
                            , andSecond = Mock.bSymbol
                            } 
                        )
                )
        )
    , testCase "patternattributes isConstructorModuloLikePattern"
        (do
            assertEqual "variables are constructor-modulo-like"
                (Right [ConstructorLikeProof])
                (isConstructorModuloLikePattern
                    Mock.metadataTools
                    (mkElemVar Mock.x)
                )
            let
                constructor :: TermLike Variable
                constructor = Mock.a
            assertEqual
                "constructors are constructor-modulo-like"
                (Right [ConstructorLikeProof])
                (isConstructorModuloLikePattern
                    Mock.metadataTools
                    constructor
                )
            let
                sortInjection :: TermLike Variable
                sortInjection = Mock.sortInjection10 Mock.aSort0
            assertEqual
                "sort injections are constructor-modulo-like"
                (Right [ConstructorLikeProof, ConstructorLikeProof])
                (isConstructorModuloLikePattern
                    Mock.metadataTools
                    sortInjection
                )
            let
                mapElement :: TermLike Variable
                mapElement = Mock.elementMap Mock.a Mock.b
            assertEqual
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
            assertEqual
                "string literals are constructor-modulo-like"
                (Right [ConstructorLikeProof])
                (isConstructorModuloLikePattern
                    Mock.metadataTools
                    str
                )
            let
                chr :: TermLike Variable
                chr = mkCharLiteral 'a'
            assertEqual
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
            assertEqual
                "domain values are constructor-modulo-like"
                (Right [ConstructorLikeProof])
                (isConstructorModuloLikePattern
                    Mock.metadataTools
                    dv
                )

            let
                functionConstant :: TermLike Variable
                functionConstant = Mock.cf
            assertEqual
                "function symbols are not constructor-modulo-like"
                (Left NonConstructorLikeHead)
                (isConstructorModuloLikePattern
                    Mock.metadataTools
                    functionConstant
                )
            let
                injectionConstant :: TermLike Variable
                injectionConstant = Mock.injective10 Mock.a
            assertEqual
                "injections are not constructor-modulo-like"
                (Left NonConstructorLikeHead)
                (isConstructorModuloLikePattern
                    Mock.metadataTools
                    injectionConstant
                )
        )
    ]
