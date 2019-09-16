{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Pattern.Created
    ( Created (..)
    ) where

import Control.DeepSeq
import Data.Hashable
    ( Hashable (hashWithSalt)
    )
import qualified Generics.SOP as SOP
import GHC.Generics
import GHC.Stack
    ( CallStack
    )

import Kore.Attribute.Synthetic
import Kore.Debug

-- | 'Created' is used for debugging patterns, specifically for finding out
-- where a pattern was created. This is a field in the attributes of a pattern,
-- and it will default to 'Nothing'. This field is populated via the smart
-- constructors in 'Kore.Internal.TermLike'.
newtype Created = Created { getCreated :: Maybe CallStack }
    deriving (Generic, Show)

instance Eq Created where
    (==) _ _ = True

instance SOP.Generic Created

instance SOP.HasDatatypeInfo Created

instance NFData Created

instance Hashable Created where
    hashWithSalt _ _ = 0

instance Debug Created

instance Functor pat => Synthetic Created pat where
    synthetic = const (Created Nothing)
