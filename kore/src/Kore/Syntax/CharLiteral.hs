{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}

module Kore.Syntax.CharLiteral
    ( CharLiteral (..)
    ) where

import           Control.DeepSeq
                 ( NFData (..) )
import           Data.Functor.Const
import           Data.Hashable
import           Data.String
                 ( fromString )
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Pattern.FreeVariables
       ( FreeVariables )
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.Unparser

{-|'CharLiteral' corresponds to the @char@ literal from the Semantics of K,
Section 9.1.1 (Lexicon).
-}
newtype CharLiteral = CharLiteral { getCharLiteral :: Char }
    deriving (Eq, GHC.Generic, Ord, Show)

instance Hashable CharLiteral

instance NFData CharLiteral

instance SOP.Generic CharLiteral

instance SOP.HasDatatypeInfo CharLiteral

instance Debug CharLiteral

instance Unparse CharLiteral where
    unparse = Pretty.squotes . fromString . escapeChar . getCharLiteral
    unparse2 = unparse

instance Ord variable => Synthetic (FreeVariables variable) (Const CharLiteral)
  where
    synthetic = const mempty
    {-# INLINE synthetic #-}

instance Synthetic Sort (Const CharLiteral) where
    synthetic = const charMetaSort
    {-# INLINE synthetic #-}
