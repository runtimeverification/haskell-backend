{-# OPTIONS_GHC -fno-warn-orphans #-}
{- |
Module      : Kore.Internal.SideCondition.Orphans
Description : Orphan instances of Serialize typeclass
Copyright   : (c) Runtime Verification, 2018-2022
License     : BSD-3-Clause
Maintainer  : dwight.guth@runtimeverification.com
-}

module Kore.Internal.SideCondition.Orphans () where

import Data.Serialize
import Kore.Internal.SideCondition.SideCondition (
    Representation,
 )

instance Serialize Representation
