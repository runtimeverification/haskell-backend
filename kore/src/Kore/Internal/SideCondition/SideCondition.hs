{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}

module Kore.Internal.SideCondition.SideCondition
    ( Representation
    , fromText
    ) where

import Prelude.Kore

import Control.DeepSeq
    ( NFData
    )
import Data.Hashable
    ( Hashable
    , Hashed
    , hashed
    )
import Data.Text
    ( Text
    )
import qualified Generics.SOP as SOP
    ( Generic
    , HasDatatypeInfo
    )
import qualified GHC.Generics as GHC

import Kore.Debug
    ( Debug
    , Diff (..)
    )

newtype Representation =
    Representation
        { getRepresentation :: Hashed Text
        }
    deriving (Eq, GHC.Generic, Hashable, NFData, Ord, Show)

instance SOP.Generic Representation

instance SOP.HasDatatypeInfo Representation

instance Debug Representation

instance Diff Representation

fromText :: Text -> Representation
fromText = Representation . hashed
