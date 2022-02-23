{- |
Module      : Kore.Builtin.Attributes
Description : Built-in attributes that are not yet implemented as real
              attributes
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

TODO(virgil): Get rid of this module and implement everything with normal
              attributes.
-}
module Kore.Builtin.Attributes (
    isConstructorModulo_,
) where

import Kore.Builtin.List.List qualified as List
import Kore.Builtin.Map.Map qualified as Map
import Kore.Builtin.Set.Set qualified as Set
import Kore.Internal.Symbol
import Prelude.Kore

{- | Is the symbol a constructor modulo associativity, commutativity and
 neutral element?
-}
isConstructorModulo_ :: Symbol -> Bool
isConstructorModulo_ symbol =
    any
        (apply symbol)
        [ List.isSymbolConcat
        , List.isSymbolElement
        , List.isSymbolUnit
        , Map.isSymbolConcat
        , Map.isSymbolElement
        , Map.isSymbolUnit
        , Set.isSymbolConcat
        , Set.isSymbolElement
        , Set.isSymbolUnit
        ]
  where
    apply pattHead f = f pattHead
