{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.StringLiteral
    ( StringLiteral (..)
    ) where

import           Control.DeepSeq
                 ( NFData (..) )
import           Data.Hashable
import           Data.Text
                 ( Text )
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

{-|'StringLiteral' corresponds to the @string@ literal from the Semantics of K,
Section 9.1.1 (Lexicon).
-}
newtype StringLiteral child = StringLiteral { getStringLiteral :: Text }
    deriving (Eq, Foldable, Functor, GHC.Generic, Ord, Show, Traversable)

instance Hashable (StringLiteral child)

instance NFData (StringLiteral child)

instance SOP.Generic (StringLiteral child)

instance SOP.HasDatatypeInfo (StringLiteral child)

instance Debug (StringLiteral child)

instance Unparse (StringLiteral child) where
    unparse = Pretty.dquotes . Pretty.pretty . escapeStringT . getStringLiteral
    unparse2 = unparse

instance
    Ord variable
    => Synthetic StringLiteral (FreeVariables variable)
  where
    synthetic = const mempty
    {-# INLINE synthetic #-}

instance
    Ord variable
    => Synthetic StringLiteral (FreeSetVariables variable)
  where
    synthetic = const mempty
    {-# INLINE synthetic #-}

instance Synthetic StringLiteral Sort where
    synthetic = const stringMetaSort
    {-# INLINE synthetic #-}
