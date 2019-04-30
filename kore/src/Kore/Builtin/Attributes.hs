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

import Data.Reflection
       ( Given, given )

import           Kore.Attribute.Symbol
                 ( StepperAttributes, isConstructor_, isSortInjection_ )
import qualified Kore.Attribute.Symbol as StepperAttributes
import qualified Kore.Builtin.List as List
import qualified Kore.Builtin.Map as Map
import qualified Kore.Builtin.Set as Set
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Syntax.Application
                 ( SymbolOrAlias )

-- | Is the symbol a constructor modulo associativity, commutativity and
-- neutral element?
isConstructorModulo_
    :: Given (SmtMetadataTools StepperAttributes)
    => SymbolOrAlias
    -> Bool
isConstructorModulo_ symbolOrAlias =
    any (apply given symbolOrAlias)
        [ List.isSymbolConcat, List.isSymbolElement, List.isSymbolUnit
        ,  Map.isSymbolConcat,  Map.isSymbolElement,  Map.isSymbolUnit
        ,  Set.isSymbolConcat,  Set.isSymbolElement,  Set.isSymbolUnit
        ]
  where
    apply tools pattHead f = f (StepperAttributes.hook <$> tools) pattHead

isConstructorModuloLike_
    :: Given (SmtMetadataTools StepperAttributes)
    => SymbolOrAlias
    -> Bool
isConstructorModuloLike_ appHead =
    isConstructorModulo_ appHead
        || isConstructor_ appHead
        || isSortInjection_ appHead
