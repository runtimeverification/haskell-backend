{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}

module Kore.Internal.SideCondition.SideCondition
    ( Representation
    , fromText
    ) where

import Control.DeepSeq
    ( NFData
    )
import Data.Hashable
    ( Hashable
    , hash
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

data Representation =
    Representation
        { representationHash :: !Int
        , representation :: !Text
        }
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic Representation

instance SOP.HasDatatypeInfo Representation

instance Debug Representation

instance Diff Representation

instance NFData Representation

instance Hashable Representation

fromText :: Text -> Representation
fromText text =
    Representation
        { representationHash = hash text
        , representation = text
        }
