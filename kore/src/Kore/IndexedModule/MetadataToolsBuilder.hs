{- |
Module      : Kore.IndexedModule.MetadataToolsBuilder
Description : Creates a MetadataTools object from an IndexedModule
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.IndexedModule.MetadataToolsBuilder (
    build,
) where

import Kore.Attribute.Sort.ConstructorsBuilder qualified as Attribute.Constructors (
    indexBySort,
 )
import Kore.Attribute.Symbol (
    StepperAttributes,
 )
import Kore.IndexedModule.IndexedModule (
    VerifiedModule,
 )
import Kore.IndexedModule.MetadataTools (
    SmtMetadataTools,
    extractMetadataTools,
 )
import Kore.Rewrite.SMT.Representation.All qualified as SMT.Representation (
    build,
 )
import Prelude.Kore ()

{- |Creates a set of 'MetadataTools' from a 'KoreIndexedModule'.

 The metadata tools are functions yielding information
 about application heads, such as its attributes or
 its argument and result sorts.
-}
build ::
    VerifiedModule StepperAttributes ->
    SmtMetadataTools StepperAttributes
build m =
    extractMetadataTools
        m
        Attribute.Constructors.indexBySort
        SMT.Representation.build
