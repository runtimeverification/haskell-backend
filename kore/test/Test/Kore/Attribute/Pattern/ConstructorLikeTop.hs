module Test.Kore.Attribute.Pattern.ConstructorLikeTop
    ( test_hasConstructorLikeTop
    ) where

import Test.Tasty

import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Domain.Builtin
    ( Builtin (..)
    , InternalInt (..)
    )
import Kore.Internal.TermLike

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty.HUnit.Ext

newtype LevelString level = LevelString String
    deriving (Eq, GHC.Generic, Show)

instance SOP.Generic (LevelString level)

instance SOP.HasDatatypeInfo (LevelString level)

instance Debug (LevelString level)

instance Diff (LevelString level)

test_hasConstructorLikeTop :: [TestTree]
test_hasConstructorLikeTop =
    [ testCase "hasConstructorLikeTop"
        (do
            assertEqual "ApplySymbolF is constructor-like-top"
                True
                $ isConstructorLikeTop (mkApplySymbol Mock.aSymbol [])
            let
                dv :: DomainValue Sort (TermLike Variable)
                dv = DomainValue
                        { domainValueSort = Mock.testSort
                        , domainValueChild = mkStringLiteral "a"
                        }

            assertEqual "DomainValueF is constructor-like-top"
                True
                $ isConstructorLikeTop (mkDomainValue dv)
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
                (isConstructorLikeTop $ mkBuiltin b)
            assertEqual "StringLiteralF is constructor-like-top"
                True
                (isConstructorLikeTop $ mkStringLiteral "")
            assertEqual "AndF is not is constructor-like-top"
                False
                (isConstructorLikeTop $ mkAnd Mock.a Mock.b)
        )
    ]
  where
    isConstructorLikeTop :: TermLike Variable -> Bool
    isConstructorLikeTop = hasConstructorLikeTop
