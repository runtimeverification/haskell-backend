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
    , extractMetadataTools
    )
  where

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.ASTHelpers
import           Data.Kore.Implicit.Attributes
import           Data.Kore.IndexedModule.IndexedModule
import           Data.Kore.IndexedModule.Resolvers

-- |'MetadataTools' defines a dictionary of functions which can be used to
-- access the metadata needed during the unification process.
data MetadataTools level = MetadataTools
    { isConstructor    :: SymbolOrAlias level -> Bool
    , isFunctional     :: SymbolOrAlias level -> Bool
    , getArgumentSorts :: SymbolOrAlias level -> [Sort level]
    , getResultSort    :: SymbolOrAlias level -> Sort level
    }

-- |'extractMetadataTools' extracts a set of 'MetadataTools' from a
-- 'KoreIndexedModule'.  The metadata tools are functions yielding information
-- about application heads, such as whether it is functional / constructor,
-- or its argument and result sorts.
--
-- Since there is no clear consensus on how constructor and functionality
-- axioms would be specified yet, we currently assume all symbols
-- are constructors and all of them are functional, too.
-- TODO: fix the above issue (maybe using attributes for the moment?)
extractMetadataTools
    :: MetaOrObject level
    => KoreIndexedModule
    -> MetadataTools level
extractMetadataTools m =
  MetadataTools
    { isConstructor    = hasAttribute constructorAttribute
    , isFunctional     = hasAttribute functionalAttribute
    , getArgumentSorts = applicationSortsOperands . getHeadApplicationSorts m
    , getResultSort    = applicationSortsResult   . getHeadApplicationSorts m
    }
    where hasAttribute
            :: MetaOrObject level
            => CommonKorePattern
            -> SymbolOrAlias level
            -> Bool
          hasAttribute attr =
            elem attr . getAttributeList m
