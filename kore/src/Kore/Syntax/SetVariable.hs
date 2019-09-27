{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.SetVariable
    ( SetVariable (..)
    ) where

import Control.DeepSeq
    ( NFData (..)
    )
import Data.Hashable
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Debug
import Kore.Unparser

-- | Applicative-Kore set variables
newtype SetVariable variable
    = SetVariable { getSetVariable :: variable }
    deriving (Eq, GHC.Generic, Ord, Show, Functor, Foldable, Traversable)

instance Hashable variable => Hashable (SetVariable variable)

instance NFData variable => NFData (SetVariable variable)

instance SOP.Generic (SetVariable variable)

instance SOP.HasDatatypeInfo (SetVariable variable)

instance Debug variable => Debug (SetVariable variable)

instance (Debug variable, Diff variable) => Diff (SetVariable variable)

instance Unparse variable => Unparse (SetVariable variable) where
    unparse = unparse . getSetVariable
    unparse2 = unparse2 . getSetVariable
