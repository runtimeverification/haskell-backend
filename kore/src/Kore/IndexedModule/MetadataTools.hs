{- |
Module      : Kore.IndexedModule.MetadataTools
Description : Datastructures and functionality for retrieving metadata
              information from patterns
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.IndexedModule.MetadataTools (
    MetadataTools(..),
    MetadataToolsData,
    SmtMetadataTools,
    extractMetadataTools,
    findSortConstructors,
) where

import Data.Map.Strict (
    Map,
 )
import Data.Map.Strict qualified as Map
import Data.Serialize
import GHC.Generics qualified as GHC
import Kore.Attribute.Sort qualified as Attribute
import Kore.Attribute.Sort.Constructors qualified as Attribute (
    Constructors,
 )
import Kore.IndexedModule.IndexedModule
import Kore.IndexedModule.Resolvers
import Kore.Internal.ApplicationSorts hiding (
    applicationSorts,
 )
import Kore.Rewrite.SMT.AST qualified as SMT.AST (
    SmtDeclarations,
 )
import Kore.Sort
import Kore.Syntax.Application (
    SymbolOrAlias (..),
 )
import Prelude.Kore

class MetadataTools metadata where
    sortAttributes :: metadata sortConstructors smt attributes -> Sort -> Attribute.Sort
    applicationSorts :: metadata sortConstructors smt attributes -> SymbolOrAlias -> ApplicationSorts
    symbolAttributes :: metadata sortConstructors smt attributes -> Id -> attributes
    smtData :: metadata sortConstructors smt attributes -> smt
    sortConstructors :: metadata sortConstructors smt attributes -> Map Id sortConstructors

{- |'MetadataTools' defines a dictionary of functions which can be used to
 access the metadata needed during the unification process.
-}
data MetadataToolsData sortConstructors smt attributes = MetadataToolsData
    { -- | syntax of module
      syntax :: VerifiedModuleSyntax attributes
    , -- | The SMT data for the given module.
      smtDataInternal :: smt
    , -- | The constructors for each sort.
      sortConstructorsInternal :: Map Id sortConstructors
    }
    deriving stock (Functor)
    deriving stock (GHC.Generic)
    deriving anyclass (Serialize)

type SmtMetadataTools metadata attributes =
    metadata Attribute.Constructors SMT.AST.SmtDeclarations attributes

{- |'extractMetadataTools' extracts a set of 'MetadataTools' from a
 'KoreIndexedModule'.  The metadata tools are functions yielding information
 about application heads, such as its attributes or
 its argument and result sorts.
-}
extractMetadataTools ::
    forall declAtts smt sortConstructors.
    VerifiedModule declAtts ->
    (VerifiedModule declAtts -> Map Id sortConstructors) ->
    (VerifiedModule declAtts -> Map Id sortConstructors -> smt) ->
    MetadataToolsData sortConstructors smt declAtts
extractMetadataTools m constructorsExtractor smtExtractor =
    MetadataToolsData
        { syntax = indexedModuleSyntax m
        , smtDataInternal = smtExtractor m constructors
        , sortConstructorsInternal = constructors
        }
  where
    constructors = constructorsExtractor m

{- | Extracts all constructors for a sort.

Should return Nothing if the sort has no constructors or if the sort has no
constructors, or `inj` behaves like a constructor, but the latter is only true
if the constructor axioms actually include `inj` when needed, which is not true
right now.
-}
findSortConstructors ::
    MetadataTools metadata =>
    SmtMetadataTools metadata attributes ->
    Id ->
    Maybe Attribute.Constructors
findSortConstructors metadataTools sortId =
    Map.lookup sortId $ sortConstructors metadataTools

instance MetadataTools MetadataToolsData where
    sortAttributes tools s = getSortAttributes (syntax tools) s
    applicationSorts tools s = getHeadApplicationSorts (syntax tools) s
    symbolAttributes tools s = getSymbolAttributes (syntax tools) s
    smtData = smtDataInternal
    sortConstructors = sortConstructorsInternal
