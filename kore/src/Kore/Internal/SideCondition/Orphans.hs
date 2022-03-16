{-# OPTIONS_GHC -fno-warn-orphans #-}
{- |
Module      : Kore.Internal.SideCondition.Orphans
Description : Orphan instances of Serialize typeclass
Copyright   : (c) Runtime Verification, 2018-2022
License     : BSD-3-Clause
Maintainer  : dwight.guth@runtimeverification.com
-}

module Kore.Internal.SideCondition.Orphans () where

import Data.Hashable
import Data.Serialize
import Data.Type.Equality (
    testEquality,
 )
import GHC.Generics qualified as GHC
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.SideCondition.SideCondition (
    Representation(..),
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Syntax.Variable
import Prelude.Kore
import Type.Reflection (
    typeOf,
    typeRep,
 )

-- SideCondition.Representation
-- located here to break circular dependency between SideCondition and TermLike
data RepresentationType
  = VariableNameType
  | RewritingVariableNameType
  deriving stock (GHC.Generic)
  deriving anyclass (Serialize)

tagOf :: (Typeable a) => Hashed a -> RepresentationType
tagOf h =
    let typeRep1 = typeOf $ unhashed h
    in case testEquality typeRep1 (typeRep @(SideCondition VariableName)) of
      Just _ -> VariableNameType
      Nothing -> case testEquality typeRep1 (typeRep @(SideCondition RewritingVariableName)) of
          Just _ -> RewritingVariableNameType
          Nothing -> error "Unknown side condition variable type when serializing"

instance Serialize Representation where
    put (Representation h) = do
        put $ tagOf h
        put h
    get = do
        tag <- get
        case tag of
            VariableNameType -> fmap Representation $ get @(Hashed (SideCondition VariableName))
            RewritingVariableNameType -> fmap Representation $ get @(Hashed (SideCondition RewritingVariableName))
