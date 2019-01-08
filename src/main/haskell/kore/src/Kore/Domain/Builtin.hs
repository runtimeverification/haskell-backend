{-|
Module      : Kore.Domain.Builtin
Description : Internal representation of builtin domains
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Domain.Builtin where

import           Control.DeepSeq
                 ( NFData (..) )
import           Data.Deriving
                 ( deriveEq1, deriveOrd1, deriveShow1 )
import qualified Data.Foldable as Foldable
import           Data.Functor.Const
                 ( Const )
import           Data.Hashable
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Sequence
                 ( Seq )
import           Data.Set
                 ( Set )
import           Data.Void
                 ( Void )
import           GHC.Generics
                 ( Generic )

import Kore.Annotation.Valid
import Kore.AST.Pure

type Key = PurePattern Object Builtin Concrete (Valid (Concrete Object) Object)

data Builtin child
    = BuiltinPattern !(ParsedPurePattern Meta (Const Void))
    | BuiltinMap !(Map Key child)
    | BuiltinList !(Seq child)
    | BuiltinSet !(Set Key)
    | BuiltinInteger Integer
    | BuiltinBool Bool
    deriving (Foldable, Functor, Generic, Traversable)

deriving instance Eq child => Eq (Builtin child)

deriving instance Ord child => Ord (Builtin child)

deriving instance Show child => Show (Builtin child)

deriveEq1 ''Builtin
deriveOrd1 ''Builtin
deriveShow1 ''Builtin

instance Hashable child => Hashable (Builtin child) where
    hashWithSalt salt =
        \case
            BuiltinPattern pat ->
                salt `hashWithSalt` (0::Int) `hashWithSalt` pat
            BuiltinMap (Map.toAscList -> map') ->
                salt `hashWithSalt` (1::Int) `hashWithSalt` map'
            BuiltinList (Foldable.toList -> list) ->
                salt `hashWithSalt` (2::Int) `hashWithSalt` list
            BuiltinSet (Foldable.toList -> set) ->
                salt `hashWithSalt` (3::Int) `hashWithSalt` set
            BuiltinInteger int ->
                salt `hashWithSalt` (4::Int) `hashWithSalt` int
            BuiltinBool bool ->
                salt `hashWithSalt` (5::Int) `hashWithSalt` bool

instance NFData child => NFData (Builtin child)
