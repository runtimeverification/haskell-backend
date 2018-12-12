{-|
Module      : Kore.Annotation.Null
Description : Empty pattern annotations
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
-}
module Kore.Annotation.Null where

import Control.DeepSeq
       ( NFData )
import Data.Hashable
       ( Hashable )
import GHC.Generics
       ( Generic )

import Kore.Reflect
       ( Reflectable )


{- | @Null@ is an empty pattern annotation
 -}
data Null level = Null
    deriving (Eq, Generic, Ord, Show)

instance NFData (Null level)

instance Hashable (Null level)

instance Semigroup (Null level) where
    (<>) _ _ = Null

instance Monoid (Null level) where
    mempty = Null
    mappend = (<>)

instance Reflectable (Null level)
