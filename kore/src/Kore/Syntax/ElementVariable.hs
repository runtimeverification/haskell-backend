{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.ElementVariable
    ( ElementVariable (..)
    ) where

import           Control.DeepSeq
                 ( NFData (..) )
import           Data.Functor.Const
import           Data.Hashable
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Unparser
import Kore.Variables.AsVariable
import Kore.Variables.UnifiedVariable

-- | Applicative-Kore set variables
newtype ElementVariable variable = ElementVariable { getVariable :: variable }
    deriving (Eq, GHC.Generic, Ord, Show)

instance Hashable variable => Hashable (ElementVariable variable)

instance NFData variable => NFData (ElementVariable variable)

instance SOP.Generic (ElementVariable variable)

instance SOP.HasDatatypeInfo (ElementVariable variable)

instance Debug variable => Debug (ElementVariable variable)

instance
    Ord variable =>
    Synthetic (Const (ElementVariable variable)) (FreeVariables variable)
  where
    synthetic (Const elemVar) = freeVariable (asUnifiedVariable elemVar)
    {-# INLINE synthetic #-}

instance Unparse variable => Unparse (ElementVariable variable) where
    unparse = unparse . asVariable
    unparse2 = unparse2 . asVariable

instance AsVariable ElementVariable where
    asVariable = getVariable

instance AsUnifiedVariable ElementVariable where
    asUnifiedVariable = ElemVar . asVariable
