{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.Arguments
    ( Arguments (Arguments, getArguments)
    , IsList (..)
    ) where

import Control.DeepSeq
    ( NFData
    )
import Data.Functor.Classes
    ( Eq1
    , Ord1
    , Read1
    , Show1
    )
import Data.Hashable
    ( Hashable
    )
import Data.Typeable
    ( Typeable
    )
import qualified Generics.SOP as SOP
import GHC.Exts
    ( IsList (..)
    )
import qualified GHC.Generics as GHC

import Debug
import Kore.Unparser

newtype Arguments a = Arguments_ [a]
    deriving (Eq, Ord, Read, Show)
    deriving (Eq1, Ord1, Read1, Show1)
    deriving (Functor, Foldable, Traversable)
    deriving (GHC.Generic, Typeable)

instance IsList (Arguments a) where
    type Item (Arguments a) = a

    toList = getArguments
    {-# INLINE toList #-}

    fromList = Arguments
    {-# INLINE fromList #-}

    fromListN _ = Arguments
    {-# INLINE fromListN #-}

instance NFData a => NFData (Arguments a)

instance Hashable a => Hashable (Arguments a)

instance SOP.Generic (Arguments a)

instance SOP.HasDatatypeInfo (Arguments a)

instance Debug a => Debug (Arguments a)

instance (Debug a, Diff a) => Diff (Arguments a)

instance Unparse a => Unparse (Arguments a) where
    unparse = arguments . getArguments
    unparse2 = arguments2 . getArguments

pattern Arguments :: [a] -> Arguments a
pattern Arguments { getArguments } = Arguments_ getArguments
