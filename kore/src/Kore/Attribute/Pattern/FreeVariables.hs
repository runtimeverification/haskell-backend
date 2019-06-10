{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables (..)
    , insert, delete, member
    ) where

import Control.DeepSeq
import Data.Set (Set)
import qualified Data.Set as Set
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP

import Kore.Debug

newtype FreeVariables variable =
    FreeVariables { getFreeVariables :: Set variable }
    deriving GHC.Generic
    deriving (Semigroup, Monoid)

instance SOP.Generic (FreeVariables variable)

instance SOP.HasDatatypeInfo (FreeVariables variable)

instance Debug variable => Debug (FreeVariables variable)

instance NFData variable => NFData (FreeVariables variable)

insert
    :: Ord variable
    => variable
    -> FreeVariables variable
    -> FreeVariables variable
insert variable (FreeVariables freeVariables) =
    FreeVariables (Set.insert variable freeVariables)
{-# INLINE insert #-}

delete
    :: Ord variable
    => variable
    -> FreeVariables variable
    -> FreeVariables variable
delete variable (FreeVariables freeVariables) =
    FreeVariables (Set.delete variable freeVariables)
{-# INLINE delete #-}

member :: Ord variable => variable -> FreeVariables variable -> Bool
member variable (FreeVariables freeVariables) =
    Set.member variable freeVariables
{-# INLINE member #-}
