{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.ElementVariable
    ( ElementVariable (..)
    ) where

import           Control.DeepSeq
                 ( NFData (..) )
import           Data.Hashable
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Debug
import Kore.Unparser
import Kore.Variables.AsVariable

-- | Applicative-Kore set variables
newtype ElementVariable variable = ElementVariable variable
    deriving (Eq, GHC.Generic, Ord, Show, Functor, Foldable, Traversable)

instance Hashable variable => Hashable (ElementVariable variable)

instance NFData variable => NFData (ElementVariable variable)

instance SOP.Generic (ElementVariable variable)

instance SOP.HasDatatypeInfo (ElementVariable variable)

instance Debug variable => Debug (ElementVariable variable)

instance Unparse variable => Unparse (ElementVariable variable) where
    unparse = unparse . asVariable
    unparse2 = unparse2 . asVariable

instance AsVariable ElementVariable where
    asVariable (ElementVariable v) = v
