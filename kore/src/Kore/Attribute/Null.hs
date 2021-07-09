{- |
Module      : Kore.Attribute.Null
Description : Null attribute parser
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
Maintainer  : thomas.tuegel@runtimeverification.com
The 'Null' attribute is used when we need a type to satisfy the attribute
parser, but we do not actually care to parse any attributes. This parser simply
ignores all attributes.
This module is intended to be imported qualified:
@
import qualified Kore.Attribute.Null as Attribute
@
-}
module Kore.Attribute.Null (
    Null (..),
) where

import Data.Default
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Debug
import Prelude.Kore

data Null = Null
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Default Null where
    def = Null

instance Semigroup Null where
    (<>) _ _ = Null

instance Monoid Null where
    mempty = Null
