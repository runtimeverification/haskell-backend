{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.SubstVar where

import           Control.DeepSeq
                 ( NFData )
import           Data.Hashable
import           GHC.Generics
                 ( Generic )
import qualified Generics.SOP as SOP

import Kore.Debug
import Kore.Unparser

{- | @SubstVar@ helps distinguish set variables (introduced by 'SetVar')
from regular variables (introduced by 'RegVar') within a substitution.
 -}
data SubstVar variable
    = RegVar variable
    | SetVar variable
    deriving (Generic, Eq, Ord, Show, Functor, Foldable, Traversable)

instance NFData variable => NFData (SubstVar variable)

instance SOP.Generic (SubstVar variable)

instance SOP.HasDatatypeInfo (SubstVar variable)

instance Debug variable => Debug (SubstVar variable)

instance Unparse variable => Unparse (SubstVar variable) where
    unparse = unparse . asVariable
    unparse2 = unparse2 . asVariable

instance Hashable variable => Hashable (SubstVar variable) where
    hashWithSalt salt (RegVar v) =
        salt `hashWithSalt` (0::Int) `hashWithSalt` v
    hashWithSalt salt (SetVar v) =
        salt `hashWithSalt` (1::Int) `hashWithSalt` v

asVariable :: SubstVar variable -> variable
asVariable (RegVar v) = v
asVariable (SetVar v) = v
