{-|
Module      : Kore.Attribute.Sort.Unit.Unit
Description : Unit sort attribute
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Sort.Unit.Unit
    ( Unit (..)
    ) where

import Control.DeepSeq
       ( NFData )
import Data.Default
import GHC.Generics
       ( Generic )

import Kore.AST.Common
import Kore.AST.MetaOrObject

-- | @Unit@ represents the @unit@ attribute for sorts.
newtype Unit = Unit { getUnit :: Maybe (SymbolOrAlias Object) }
    deriving (Generic, Eq, Ord, Show)

instance Semigroup Unit where
    (<>) a@(Unit (Just _)) _ = a
    (<>) _                     b = b

instance Monoid Unit where
    mempty = Unit { getUnit = Nothing }

instance Default Unit where
    def = mempty

instance NFData Unit
