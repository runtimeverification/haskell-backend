{-|
Module      : Kore.Implicit.Definitions
Description : Builds the implicit kore Definitions.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}

module Kore.Implicit.Definitions
    ( uncheckedKoreDefinition
    , uncheckedKoreModules
    , uncheckedMetaDefinition
    , MetaModule
    , MetaDefinition
    ) where

import Data.Functor.Const
       ( Const )
import Data.Void
       ( Void )

import           Kore.AST.MetaOrObject
                 ( Meta )
import qualified Kore.AST.Pure as AST.Pure
import           Kore.AST.PureToKore
                 ( modulePureToKore )
import           Kore.AST.Sentence
import           Kore.Implicit.ImplicitKore
                 ( uncheckedKoreModule )

type MetaModule = PureModule Meta (Const Void)
type MetaDefinition = PureDefinition Meta (Const Void)

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
    map modulePureToKore (castModuleDomainValues <$> metaModules)
  where
    castModuleDomainValues = (fmap . fmap) AST.Pure.castVoidDomainValues

{-| 'uncheckedKoreDefinition' contains all the implicit modules as 'KoreModule'.
Does not do any validation for these modules.
-}
uncheckedKoreDefinition :: KoreDefinition
uncheckedKoreDefinition =
    Definition
        { definitionAttributes = Attributes []
        , definitionModules    = uncheckedKoreModules
        }
