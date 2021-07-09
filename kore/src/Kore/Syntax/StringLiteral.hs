{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Syntax.StringLiteral (
    StringLiteral (..),
) where

import Data.Functor.Const
import Data.Text (
    Text,
 )
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Pattern.FreeVariables (
    FreeVariables,
    emptyFreeVariables,
 )
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.Unparser
import Prelude.Kore
import qualified Pretty

{- |'StringLiteral' corresponds to the @string@ literal from the Semantics of K,
Section 9.1.1 (Lexicon).
-}
newtype StringLiteral = StringLiteral {getStringLiteral :: Text}
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse StringLiteral where
    unparse = Pretty.dquotes . Pretty.pretty . escapeStringT . getStringLiteral
    unparse2 = unparse

instance Synthetic (FreeVariables variable) (Const StringLiteral) where
    synthetic = const emptyFreeVariables
    {-# INLINE synthetic #-}

instance Synthetic Sort (Const StringLiteral) where
    synthetic = const stringMetaSort
    {-# INLINE synthetic #-}
