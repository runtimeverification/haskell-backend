module Test.Kore.Proof.Functional
    ( test_mapVariables
    ) where

import Test.Tasty

import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Internal.TermLike
import Kore.Proof.Functional as Proof.Functional

import qualified Test.Kore.Step.MockSymbols as MockSymbols
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

test_mapVariables :: [TestTree]
test_mapVariables =
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
    ]

