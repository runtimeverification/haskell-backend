{-|
Module      : Kore.Attribute.Null
Description : Null attribute parser
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

The 'Null' attribute is used when we need a type to satisfy the attribute
parser, but we do not actually care to parse any attributes. This parser simply
ignores all attributes.

This module is intended to be imported qualified:
@
import qualified Kore.Attribute.Null as Attribute
@

-}
{-# LANGUAGE Strict #-}
module Kore.Attribute.Null
    ( Null (..)
    ) where

import Prelude.Kore

import Data.Default
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Debug

data Null = Null
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving anyclass (NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Default Null where
    def = Null

instance Semigroup Null where
    (<>) _ _ = Null

instance Monoid Null where
    mempty = Null
