{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.Variables.UnifiedVariable where

import           Control.DeepSeq
                 ( NFData )
import           Data.Hashable
import qualified Generics.SOP as SOP
import           GHC.Generics
                 ( Generic )

import Kore.Debug
import Kore.Variables.AsVariable
import Kore.Unparser

{- | @UnifiedVariable@ helps distinguish set variables (introduced by 'SetVar')
from element variables (introduced by 'ElemVar').
 -}
data UnifiedVariable variable
    = ElemVar variable
    | SetVar variable
    deriving (Generic, Eq, Ord, Show, Functor, Foldable, Traversable)

instance NFData variable => NFData (UnifiedVariable variable)

instance SOP.Generic (UnifiedVariable variable)

instance SOP.HasDatatypeInfo (UnifiedVariable variable)

instance Debug variable => Debug (UnifiedVariable variable)

instance Hashable variable => Hashable (UnifiedVariable variable)

instance Unparse variable => Unparse (UnifiedVariable variable) where
    unparse = unparse . asVariable
    unparse2 = unparse2 . asVariable

isSetVar :: UnifiedVariable variable -> Bool
isSetVar (SetVar _) = True
isSetVar _ = False

class AsUnifiedVariable f where
    asUnifiedVariable :: f variable -> UnifiedVariable variable

instance AsVariable UnifiedVariable where
    asVariable (ElemVar v) = v
    asVariable (SetVar v) = v
