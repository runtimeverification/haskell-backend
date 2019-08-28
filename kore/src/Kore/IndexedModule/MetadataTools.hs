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
    , SmtMetadataTools
    , extractMetadataTools
    ) where

import           Data.Graph
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Maybe
                 ( mapMaybe )
import           Data.Set
                 ( Set )
import qualified Data.Set as Set

import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Sort as Attribute
import           Kore.Attribute.Subsort
import           Kore.IndexedModule.IndexedModule
import           Kore.IndexedModule.Resolvers
import           Kore.Internal.ApplicationSorts
import           Kore.Sort
import qualified Kore.Step.SMT.AST as SMT.AST
                 ( SmtDeclarations )
import           Kore.Syntax.Application
                 ( SymbolOrAlias (..) )

-- |'MetadataTools' defines a dictionary of functions which can be used to
-- access the metadata needed during the unification process.
data MetadataTools smt attributes = MetadataTools
    { sortAttributes :: Sort -> Attribute.Sort
    -- ^ get the attributes of a sort
    , isSubsortOf :: Sort -> Sort -> Bool
    {- ^ @isSubsortOf a b@ is true if sort @a@ is a subsort of sort @b@,
       including when @a@ equals @b@. -}
    , subsorts :: Sort -> Set Sort
    -- ^ get the subsorts for a sort
    , applicationSorts :: SymbolOrAlias -> ApplicationSorts
    -- ^ Sorts for a specific symbol application.
    , symbolAttributes :: Id -> attributes
    -- ^ get the attributes of a symbol
    , isOverloading :: SymbolOrAlias -> SymbolOrAlias -> Bool
    -- ^ whether the first argument is overloading the second
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
    ::  forall declAtts smt.
        VerifiedModule declAtts Attribute.Axiom
    ->  (  VerifiedModule declAtts Attribute.Axiom
        -> smt
        )
    -> MetadataTools smt declAtts
extractMetadataTools m smtExtractor =
    MetadataTools
        { sortAttributes = getSortAttributes m
        , isSubsortOf = checkSubsort
        , subsorts = Set.fromList . fmap getSortFromId . getSubsorts
        , applicationSorts = getHeadApplicationSorts m
        , symbolAttributes = getSymbolAttributes m
        , isOverloading = checkOverloading
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

    overloads =
        Set.fromList
        $ mapMaybe
            (Attribute.getOverload . Attribute.overload . fst)
            (recursiveIndexedModuleAxioms m)

    checkOverloading :: SymbolOrAlias -> SymbolOrAlias -> Bool
    checkOverloading =
        let
            realCheckOverloading head1 head2 =
                (head1, head2) `Set.member` overloads
        in realCheckOverloading
