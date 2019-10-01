{-|
Module      : Kore.IndexedModule.MetadataToolsBuilder
Description : Creates a MetadataTools object from an IndexedModule
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.IndexedModule.MetadataToolsBuilder
    ( build
    ) where

import qualified Kore.Attribute.Axiom as Attribute
    ( Axiom
    )
import qualified Kore.Attribute.Sort.ConstructorsBuilder as Attribute.Constructors
    ( indexBySort
    )
import Kore.Attribute.Symbol
    ( StepperAttributes
    )
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    )
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    , extractMetadataTools
    )
import qualified Kore.Step.SMT.Representation.All as SMT.Representation
    ( build
    )


-- |Creates a set of 'MetadataTools' from a 'KoreIndexedModule'.
--
-- The metadata tools are functions yielding information
-- about application heads, such as its attributes or
-- its argument and result sorts.
--
build
    :: VerifiedModule StepperAttributes Attribute.Axiom
    -> SmtMetadataTools StepperAttributes
build m =
    extractMetadataTools
        m
        Attribute.Constructors.indexBySort
        SMT.Representation.build
