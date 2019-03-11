{-|
Module      : Kore.Attribute.Sort.Element.Element
Description : Element sort attribute
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Sort.Element.Element
    ( Element (..)
    ) where

import Control.DeepSeq
       ( NFData )
import Data.Default
import GHC.Generics
       ( Generic )

import Kore.AST.Common
import Kore.AST.MetaOrObject

-- | @Element@ represents the @element@ attribute for sorts.
newtype Element = Element { getElement :: Maybe (SymbolOrAlias Object) }
    deriving (Generic, Eq, Ord, Show)

instance Semigroup Element where
    (<>) a@(Element (Just _)) _ = a
    (<>) _                     b = b

instance Monoid Element where
    mempty = Element { getElement = Nothing }

instance Default Element where
    def = mempty

instance NFData Element
