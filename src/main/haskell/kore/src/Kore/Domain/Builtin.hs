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

import Kore.AST.Pure
import Kore.Reflect
       ( Reflectable )

data Builtin child
    = BuiltinPattern !(CommonPurePattern Meta (Const Void))
    | BuiltinMap !(Map (ConcretePurePattern Object Builtin) child)
    | BuiltinList !(Seq child)
    | BuiltinSet !(Set (ConcretePurePattern Object Builtin))
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

instance NFData child => NFData (Builtin child)

instance Reflectable child => Reflectable (Builtin child)
