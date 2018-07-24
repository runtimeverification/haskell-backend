{-|
Module      : Data.Kore.IndexedModule.MetadataTools
Description : Datastructures and functionality for retrieving metadata
              information from patterns
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Data.Kore.IndexedModule.MetadataTools
    ( MetadataTools (..)
    , SortTools (..)
    , extractMetadataTools
    )
  where

import           Data.Kore.AST.Common
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.ASTHelpers
import           Data.Kore.IndexedModule.IndexedModule
import           Data.Kore.IndexedModule.Resolvers

-- |'MetadataTools' defines a dictionary of functions which can be used to
-- access the metadata needed during the unification process.
data MetadataTools level attributes = MetadataTools
    { attributes :: SymbolOrAlias level -> attributes
    , sortTools  :: SortTools level
    }

data SortTools level =
    SortTools
    { getArgumentSorts :: SymbolOrAlias level -> [Sort level]
    , getResultSort    :: SymbolOrAlias level -> Sort level
    }

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
    { attributes    = getHeadAttributes m
    , sortTools =
      SortTools
      { getArgumentSorts = applicationSortsOperands . getHeadApplicationSorts m
      , getResultSort    = applicationSortsResult   . getHeadApplicationSorts m
      }
    }
