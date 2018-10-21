{-|
Module      : Kore.IndexedModule.MetadataTools
Description : Datastructures and functionality for retrieving metadata
              information from patterns
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.IndexedModule.MetadataTools
    ( MetadataTools (..)
    , SymbolOrAliasSorts
    , extractMetadataTools
    , getResultSort
    ) where

import           Data.Graph
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map

import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.ASTHelpers
       ( ApplicationSorts (..) )
import Kore.Attribute.Subsort
import Kore.IndexedModule.IndexedModule
import Kore.IndexedModule.Resolvers

-- |'MetadataTools' defines a dictionary of functions which can be used to
-- access the metadata needed during the unification process.
data MetadataTools level attributes = MetadataTools
    { symAttributes :: SymbolOrAlias level -> attributes
    -- ^ get the attributes of a symbol or alias
    , sortAttributes :: Sort level -> attributes
    -- ^ get the attributes of a sort
    , symbolOrAliasSorts :: SymbolOrAliasSorts level
    -- ^ get the signature of a symbol or alias
    , isSubsortOf :: Sort level -> Sort level -> Bool
    {- ^ @isSubsortOf a b@ is true if sort @a@ is a subsort of sort @b@,
       including when @a@ equals @b@. -}
    }
  deriving Functor

type SymbolOrAliasSorts level = SymbolOrAlias level -> ApplicationSorts level

-- |'extractMetadataTools' extracts a set of 'MetadataTools' from a
-- 'KoreIndexedModule'.  The metadata tools are functions yielding information
-- about application heads, such as its attributes or
-- its argument and result sorts.
--
extractMetadataTools
    ::forall level atts . MetaOrObject level
    => KoreIndexedModule atts
    -> MetadataTools level atts
extractMetadataTools m =
  MetadataTools
    { symAttributes = getHeadAttributes m
    , sortAttributes = getSortAttributes m
    , symbolOrAliasSorts  = getHeadApplicationSorts m
    , isSubsortOf = checkSubsort
    }
  where
    checkSubsort = case isMetaOrObject @level [] of
        IsMeta -> (==)
        IsObject ->
            let
                subsortTable :: Map (Sort Object) [Sort Object]
                subsortTable = Map.unionsWith (++)
                   [ Map.insert subsort [] $ Map.singleton supersort [subsort]
                   | Subsort subsort supersort <- indexedModuleSubsorts m]
                (sortGraph, _, getSortId) =
                    graphFromEdges [ ((),supersort,subsorts)
                                   | (supersort,subsorts)
                                     <- Map.toList subsortTable]
                realCheckSubsort subsort supersort
                    | Just subId <- getSortId subsort
                    , Just supId <- getSortId supersort =
                          path sortGraph supId subId
                realCheckSubsort _ _ = False
            in realCheckSubsort

{- | Look up the result sort of a symbol or alias
 -}
getResultSort :: MetadataTools level attrs -> SymbolOrAlias level -> Sort level
getResultSort tools symbol =
    applicationSortsResult (symbolOrAliasSorts tools symbol)
