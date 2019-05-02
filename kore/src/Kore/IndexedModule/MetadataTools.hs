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
    ( HeadType (..)
    , MetadataTools (..)
    , SmtMetadataTools
    , extractMetadataTools
    ) where

import           Data.Graph
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Set
                 ( Set )
import qualified Data.Set as Set

import           Kore.ASTHelpers
                 ( ApplicationSorts )
import qualified Kore.Attribute.Sort as Attribute
import           Kore.Attribute.Subsort
import           Kore.IndexedModule.IndexedModule
import           Kore.IndexedModule.Resolvers
import           Kore.Sort
import qualified Kore.Step.SMT.AST as SMT.AST
                 ( SmtDeclarations )
import           Kore.Syntax.Application
                 ( SymbolOrAlias (..) )

-- |'MetadataTools' defines a dictionary of functions which can be used to
-- access the metadata needed during the unification process.
data MetadataTools smt attributes = MetadataTools
    { symAttributes :: SymbolOrAlias -> attributes
    -- ^ get the attributes of a symbol or alias
    , symbolOrAliasType :: SymbolOrAlias -> HeadType
    -- ^ whether a symbol or alias is a symbol
    , sortAttributes :: Sort -> Attribute.Sort
    -- ^ get the attributes of a sort
    , isSubsortOf :: Sort -> Sort -> Bool
    {- ^ @isSubsortOf a b@ is true if sort @a@ is a subsort of sort @b@,
       including when @a@ equals @b@. -}
    , subsorts :: Sort -> Set Sort
    -- ^ get the subsorts for a sort
    , applicationSorts :: SymbolOrAlias -> ApplicationSorts
    -- ^ Sorts for a specific symbol application.
    , smtData :: smt
    -- ^ The SMT data for the given module.
    }
  deriving Functor

type SmtMetadataTools attributes =
    MetadataTools SMT.AST.SmtDeclarations attributes

-- |'extractMetadataTools' extracts a set of 'MetadataTools' from a
-- 'KoreIndexedModule'.  The metadata tools are functions yielding information
-- about application heads, such as its attributes or
-- its argument and result sorts.
--
extractMetadataTools
    ::  forall declAtts axiomAtts smt.
        VerifiedModule declAtts axiomAtts
    ->  (  VerifiedModule declAtts axiomAtts
        -> smt
        )
    -> MetadataTools smt declAtts
extractMetadataTools m smtExtractor =
    MetadataTools
        { symAttributes = getHeadAttributes m
        , symbolOrAliasType = getHeadType m
        , sortAttributes = getSortAttributes m
        , isSubsortOf = checkSubsort
        , subsorts = Set.fromList . fmap getSortFromId . getSubsorts
        , applicationSorts = getHeadApplicationSorts m
        , smtData = smtExtractor m
        }
  where
    subsortTable :: Map Sort [Sort]
    subsortTable = Map.unionsWith (++)
        [ Map.insert subsort [] $ Map.singleton supersort [subsort]
        | Subsort subsort supersort <- indexedModuleSubsorts m]

    -- In `sortGraph`, an edge (a, b) represents a subsort relationship between
    -- b and a.
    (sortGraph, vertexToSort, sortToVertex) =
        graphFromEdges [ ((),supersort,subsorts)
                        | (supersort,subsorts)
                            <- Map.toList subsortTable]
    getSortFromId :: Vertex -> Sort
    getSortFromId sortId =
        let (_, sort, _) = vertexToSort sortId
        in sort

    getSubsorts :: Sort -> [Vertex]
    getSubsorts = maybe [] (reachable sortGraph) . sortToVertex

    checkSubsort :: Sort -> Sort -> Bool
    checkSubsort =
        let
            realCheckSubsort subsort supersort
              | Just subId <- sortToVertex subsort
              , Just supId <- sortToVertex supersort =
                path sortGraph supId subId
            realCheckSubsort _ _ = False
        in realCheckSubsort
