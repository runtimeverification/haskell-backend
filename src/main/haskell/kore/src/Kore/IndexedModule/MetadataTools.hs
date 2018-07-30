{-|
Module      : Kore.IndexedModule.MetadataTools
Description : Datastructures and functionality for retrieving metadata
              information from patterns
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.IndexedModule.MetadataTools
    ( MetadataTools (..)
    , SortTools
    , extractMetadataTools
    ) where

import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.ASTHelpers
import Kore.IndexedModule.IndexedModule
import Kore.IndexedModule.Resolvers

-- |'MetadataTools' defines a dictionary of functions which can be used to
-- access the metadata needed during the unification process.
data MetadataTools level attributes = MetadataTools
    { attributes :: SymbolOrAlias level -> attributes
    , sortTools  :: SortTools level
    }

type SortTools level = SymbolOrAlias level -> ApplicationSorts level

-- |'extractMetadataTools' extracts a set of 'MetadataTools' from a
-- 'KoreIndexedModule'.  The metadata tools are functions yielding information
-- about application heads, such as its attributes or
-- its argument and result sorts.
--
extractMetadataTools
    :: MetaOrObject level
    => KoreIndexedModule atts
    -> MetadataTools level atts
extractMetadataTools m =
  MetadataTools
    { attributes = getHeadAttributes m
    , sortTools  = getHeadApplicationSorts m
    }
