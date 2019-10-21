module Test.Kore.Step.PatternAttributes
    ( test_patternAttributes
    ) where

import Test.Tasty

import Data.Functor.Const
    ( Const (..)
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Domain.Builtin
    ( Builtin (..)
    , InternalInt (..)
    )
import Kore.Internal.TermLike
import Kore.Proof.Functional as Proof.Functional
import Kore.Step.PatternAttributes

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
    [ testCase "variable mapping"
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
        )
    , testCase "isConstructorLikeTop"
        (do
            let
                app :: Application Symbol child
                app = Application
                        { applicationSymbolOrAlias = Mock.aSymbol
                        , applicationChildren = undefined
                        }
            assertEqual "ApplySymbolF is constructor-like-top"
                True
                (isConstructorLikeTop
                    Mock.metadataTools
                    $ undefined :< ApplySymbolF app
                )
            let
                dv :: DomainValue Sort Symbol
                dv = DomainValue
                        { domainValueSort = Mock.testSort
                        , domainValueChild = Mock.aSymbol
                        }
            assertEqual "DomainValueF is constructor-like-top"
                True
                (isConstructorLikeTop
                    Mock.metadataTools
                    $ undefined :< DomainValueF dv
                )
            let
                b :: Kore.Domain.Builtin.Builtin key child
                b = BuiltinInt
                        (InternalInt
                            { builtinIntSort = Mock.intSort
                            , builtinIntValue = 1
                            }
                        )
            assertEqual "BuiltinF is constructor-like-top"
                True
                (isConstructorLikeTop
                    Mock.metadataTools
                    $ undefined :< BuiltinF b
                )
            let
                sl :: Const StringLiteral b
                sl = Const ( StringLiteral { getStringLiteral = mempty } )
            assertEqual "StringLiteralF is constructor-like-top"
                True
                (isConstructorLikeTop
                    Mock.metadataTools
                    $ undefined :< StringLiteralF sl
                )
            let
                a :: And Sort Symbol
                a = And
                        { andSort = Mock.testSort
                        , andFirst = Mock.aSymbol
                        , andSecond = Mock.bSymbol
                        }
            assertEqual "AndF is not is constructor-like-top"
                False
                (isConstructorLikeTop
                    Mock.metadataTools
                    $ undefined :< AndF a
                )
        )
    ]
