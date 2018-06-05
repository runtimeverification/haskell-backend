{-|
Module      : Data.Kore.Implicit.Definitions
Description : Builds the implicit kore Definitions.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}

module Data.Kore.Implicit.Definitions
    ( uncheckedAttributesDefinition
    , uncheckedKoreDefinition
    , uncheckedKoreModules
    , uncheckedMetaDefinition
    ) where

import           Data.Kore.AST.Common
import           Data.Kore.AST.Sentence
import           Data.Kore.AST.Kore
import           Data.Kore.AST.PureToKore        (modulePureToKore)
import           Data.Kore.Implicit.Attributes   (uncheckedAttributesModule)
import           Data.Kore.Implicit.ImplicitKore (uncheckedKoreModule)
import           Data.Kore.MetaML.AST

metaModules :: [MetaModule]
metaModules = [uncheckedKoreModule]

{-| 'uncheckedMetaDefinition' contains all the implicit modules as 'MetaModule'.
Does not do any validation for these modules.
-}
uncheckedMetaDefinition :: MetaDefinition
uncheckedMetaDefinition =
    Definition
        { definitionAttributes = Attributes []
        , definitionModules    = metaModules
        }

{-| 'uncheckedKoreModules' is the list of all the implicit modules as
'KoreModule'. Does not do any validation for these modules.
-}
uncheckedKoreModules :: [KoreModule]
uncheckedKoreModules =
    map modulePureToKore metaModules

{-| 'uncheckedKoreDefinition' contains all the implicit modules as 'KoreModule'.
Does not do any validation for these modules.
-}
uncheckedKoreDefinition :: KoreDefinition
uncheckedKoreDefinition =
    Definition
        { definitionAttributes = Attributes []
        , definitionModules    = uncheckedKoreModules
        }

{-| 'uncheckedAttributesDefinition' contains the module with
definitions for everything that is visible in attributes.
Does not do any validation for this module.
-}
uncheckedAttributesDefinition :: KoreDefinition
uncheckedAttributesDefinition =
    Definition
        { definitionAttributes = Attributes []
        , definitionModules    = [uncheckedAttributesModule]
        }
