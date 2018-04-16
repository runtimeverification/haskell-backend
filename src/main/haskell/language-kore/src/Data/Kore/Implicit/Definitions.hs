{-|
Module      : Data.Kore.Implicit.Definitions
Description : Builds the implicit kore Definitions.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}

module Data.Kore.Implicit.Definitions ( uncheckedKoreDefinition
                                      , uncheckedKoreModules
                                      , uncheckedMetaDefinition
                                      ) where

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.Implicit.Attributes   (uncheckedAttributesModule)
import           Data.Kore.Implicit.ImplicitKore (uncheckedKoreModule)
import           Data.Kore.MetaML.AST
import           Data.Kore.MetaML.MetaToKore     (moduleMetaToKore)

metaModules :: [MetaModule]
metaModules = [uncheckedKoreModule]

uncheckedMetaDefinition :: MetaDefinition
uncheckedMetaDefinition =
    Definition
        { definitionAttributes = Attributes []
        , definitionModules    = metaModules
        }

uncheckedKoreModules :: [KoreModule]
uncheckedKoreModules =
    uncheckedAttributesModule
    : map moduleMetaToKore metaModules

uncheckedKoreDefinition :: KoreDefinition
uncheckedKoreDefinition =
    Definition
        { definitionAttributes = Attributes []
        , definitionModules    = uncheckedKoreModules
        }
