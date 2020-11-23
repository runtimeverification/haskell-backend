{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}
module Kore.Internal.InternalInt
    ( InternalInt (..)
    ) where

import Prelude.Kore

import Control.DeepSeq
    ( NFData
    )
import Data.Functor.Const
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables
    , emptyFreeVariables
    )
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.Unparser
import qualified Pretty

{- | Internal representation of the builtin @INT.Int@ domain.
 -}
data InternalInt =
    InternalInt { internalIntSort :: !Sort, internalIntValue :: !Integer }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse InternalInt where
    unparse InternalInt { internalIntSort, internalIntValue } =
        "\\dv"
        <> parameters [internalIntSort]
        <> Pretty.parens (Pretty.dquotes $ Pretty.pretty internalIntValue)

    unparse2 InternalInt { internalIntSort, internalIntValue } =
        "\\dv2"
        <> parameters2 [internalIntSort]
        <> arguments' [Pretty.dquotes $ Pretty.pretty internalIntValue]

instance Synthetic Sort (Const InternalInt) where
    synthetic (Const InternalInt { internalIntSort }) = internalIntSort

instance Synthetic (FreeVariables variable) (Const InternalInt) where
    synthetic _ = emptyFreeVariables
