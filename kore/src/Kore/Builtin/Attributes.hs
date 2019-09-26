{- |
Module      : Kore.Builtin.Attributes
Description : Built-in attributes that are not yet implemented as real
              attributes
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

TODO(virgil): Get rid of this module and implement everything with normal
              attributes.
-}

module Kore.Builtin.Attributes
    ( isConstructorModulo_
    , isConstructorModuloLike_
    ) where

import qualified Kore.Builtin.List.List as List
import qualified Kore.Builtin.Map.Map as Map
import qualified Kore.Builtin.Set.Set as Set
import Kore.Internal.Symbol

-- | Is the symbol a constructor modulo associativity, commutativity and
-- neutral element?
isConstructorModulo_ :: Symbol -> Bool
isConstructorModulo_ symbol =
    any (apply symbol)
        [ List.isSymbolConcat, List.isSymbolElement, List.isSymbolUnit
        ,  Map.isSymbolConcat,  Map.isSymbolElement,  Map.isSymbolUnit
        ,  Set.isSymbolConcat,  Set.isSymbolElement,  Set.isSymbolUnit
        ]
  where
    apply pattHead f = f pattHead

isConstructorModuloLike_ :: Symbol -> Bool
isConstructorModuloLike_ =
    or <$> sequence [isConstructorModulo_, isConstructor, isSortInjection]
