{-# LANGUAGE TemplateHaskell #-}

module Kore.Domain.External
    ( External (..)
    , CommonExternalPattern
    ) where

import Control.DeepSeq
       ( NFData )
import Data.Deriving
       ( deriveEq1, deriveOrd1, deriveShow1 )
import Data.Functor.Const
       ( Const )
import Data.Hashable
       ( Hashable )
import Data.Void
       ( Void )
import GHC.Generics
       ( Generic )

import Kore.AST.Common
import Kore.AST.MetaOrObject

newtype External child =
    External { getExternal :: CommonPurePattern Meta (Const Void) }
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

deriveEq1 ''External
deriveOrd1 ''External
deriveShow1 ''External

instance NFData (External child)

instance Hashable (External child)

type CommonExternalPattern lvl = CommonPurePattern lvl External
