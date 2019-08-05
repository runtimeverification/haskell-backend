{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}

module Kore.Syntax.CharLiteral
    ( CharLiteral (..)
    ) where

import           Control.DeepSeq
                 ( NFData (..) )
import           Data.Hashable
import           Data.String
                 ( fromString )
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Pattern.FreeSetVariables
       ( FreeSetVariables )
import Kore.Attribute.Pattern.FreeVariables
       ( FreeVariables )
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.Unparser

{-|'CharLiteral' corresponds to the @char@ literal from the Semantics of K,
Section 9.1.1 (Lexicon).
-}
newtype CharLiteral child = CharLiteral { getCharLiteral :: Char }
    deriving (Eq, Foldable, Functor, GHC.Generic, Ord, Show, Traversable)

instance Hashable (CharLiteral child)

instance NFData (CharLiteral child)

instance SOP.Generic (CharLiteral child)

instance SOP.HasDatatypeInfo (CharLiteral child)

instance Debug (CharLiteral child)

instance Unparse (CharLiteral child) where
    unparse = Pretty.squotes . fromString . escapeChar . getCharLiteral
    unparse2 = unparse

instance
    Ord variable =>
    Synthetic CharLiteral (FreeVariables variable)
  where
    synthetic = const mempty
    {-# INLINE synthetic #-}

instance
    Ord variable =>
    Synthetic CharLiteral (FreeSetVariables variable)
  where
    synthetic = const mempty
    {-# INLINE synthetic #-}

instance Synthetic CharLiteral Sort where
    synthetic = const charMetaSort
    {-# INLINE synthetic #-}
