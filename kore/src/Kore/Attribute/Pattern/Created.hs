{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Pattern.Created
    ( Created (..)
    ) where

import           Control.DeepSeq
import qualified Generics.SOP as SOP
import           GHC.Generics
import           GHC.Stack
                 ( CallStack )

import Kore.Attribute.Synthetic
import Kore.Debug

newtype Created = Created { getCreated :: Maybe CallStack }
    deriving (Generic, Show)

instance Eq Created where
    (==) _ _ = True

instance SOP.Generic Created

instance SOP.HasDatatypeInfo Created

instance NFData Created

instance Debug Created

instance Functor pat => Synthetic Created pat where
    synthetic = const (Created Nothing)
