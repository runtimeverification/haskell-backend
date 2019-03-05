{-|
Module      : Kore.Attribute.Sort.Concat.Concat
Description : Concat sort attribute
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Sort.Concat.Concat
    ( Concat (..)
    ) where

import Control.DeepSeq
       ( NFData )
import Data.Default
import GHC.Generics
       ( Generic )

import Kore.AST.Common
import Kore.AST.MetaOrObject

-- | @Concat@ represents the @concat@ attribute for sorts.
newtype Concat = Concat { getConcat :: Maybe (SymbolOrAlias Object) }
    deriving (Generic, Eq, Ord, Show)

instance Semigroup Concat where
    (<>) a@(Concat (Just _)) _ = a
    (<>) _                     b = b

instance Monoid Concat where
    mempty = Concat { getConcat = Nothing }

instance Default Concat where
    def = mempty

instance NFData Concat
