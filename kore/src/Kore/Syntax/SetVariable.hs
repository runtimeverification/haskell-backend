{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.SetVariable
    ( SetVariable (..)
    ) where

import Control.DeepSeq
       ( NFData (..) )
import Data.Hashable
import GHC.Generics
       ( Generic )

import Kore.Unparser

-- | Applicative-Kore set variables
newtype SetVariable variable = SetVariable { getVariable :: variable }
    deriving (Show, Eq, Ord, Generic)

instance Hashable variable => Hashable (SetVariable variable)

instance NFData variable => NFData (SetVariable variable)

instance Unparse variable => Unparse (SetVariable variable) where
    unparse = unparse . getVariable
    unparse2 = unparse2 . getVariable  -- TOFIX: print with a leading "#"
