{-# OPTIONS_GHC -fno-warn-orphans #-}
{- |
Module      : Data.Serialize.Orphans
Description : Orphan instances of Serialize typeclass
Copyright   : (c) Runtime Verification, 2018-2022
License     : BSD-3-Clause
Maintainer  : dwight.guth@runtimeverification.com
-}

module Data.Serialize.Orphans () where

import Control.Comonad.Trans.Cofree
import Data.Functor.Const
import Data.Functor.Identity
import Data.Hashable
import Data.HashMap.Strict
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet
import Data.HashSet qualified as HashSet
import Data.List.NonEmpty
import Data.Serialize
import Data.Text
import Data.Text.Encoding
import Data.Void
import GHC.Generics
import Prelude.Kore

-- Text
instance Serialize Text where
  put txt = put $ encodeUtf8 txt
  get     = fmap decodeUtf8 get

-- Const
deriving anyclass instance Serialize a => Serialize (Const a b)

-- Cofree
deriving stock instance Generic (Cofree f a)
instance (Serialize a, Serialize (f (Cofree f a))) => Serialize (Cofree f a)
deriving newtype instance Serialize a => Serialize (Identity a)
instance (Serialize a, Serialize (f b)) => Serialize (CofreeF f a b)

-- Hashable
instance (Hashable a, Serialize a) => Serialize (Hashed a) where
  put h = put $ unhashed h
  get   = fmap hashed get

-- HashMap
instance (Serialize key, Eq key, Hashable key, Serialize value) => Serialize (HashMap key value) where
  put m = put $ HashMap.toList m
  get   = fmap HashMap.fromList get

-- HashSet
instance (Serialize item, Eq item, Hashable item) => Serialize (HashSet item) where
  put s = put $ HashSet.toList s
  get   = fmap HashSet.fromList get

-- Void
instance Serialize Void where
  put = absurd
  get = mzero

-- NonEmpty
deriving anyclass instance Serialize a => Serialize (NonEmpty a)
