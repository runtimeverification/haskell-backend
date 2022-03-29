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
    MetadataTools (..),
    SmtMetadataTools,
    extractMetadataTools,
    findSortConstructors,
) where

import Data.Map.Strict (
    Map,
 )
import Data.Map.Strict qualified as Map
import Kore.Attribute.Sort qualified as Attribute
import Kore.Attribute.Sort.Constructors qualified as Attribute (
    Constructors,
 )
import Kore.IndexedModule.IndexedModule
import Kore.IndexedModule.Resolvers
import Kore.Internal.ApplicationSorts
import Kore.Rewrite.SMT.AST qualified as SMT.AST (
    SmtDeclarations,
 )
import Kore.Sort
import Kore.Syntax.Application (
    SymbolOrAlias (..),
 )
import Prelude.Kore

{- |'MetadataTools' defines a dictionary of functions which can be used to
 access the metadata needed during the unification process.
-}
data MetadataTools sortConstructors smt attributes = MetadataTools
    { -- | get the attributes of a sort
      sortAttributes :: Sort -> Attribute.Sort
    , -- | Sorts for a specific symbol application.
      applicationSorts :: SymbolOrAlias -> ApplicationSorts
    , -- | get the attributes of a symbol
      symbolAttributes :: Id -> attributes
    , -- | The SMT data for the given module.
      smtData :: smt
    , -- | The constructors for each sort.
      sortConstructors :: Map Id sortConstructors
    }
    deriving stock (Functor)

type SmtMetadataTools attributes =
    MetadataTools Attribute.Constructors SMT.AST.SmtDeclarations attributes

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
    MetadataTools sortConstructors smt declAtts
extractMetadataTools m constructorsExtractor smtExtractor =
    MetadataTools
        { sortAttributes = getSortAttributes m
        , applicationSorts = getHeadApplicationSorts m
        , symbolAttributes = getSymbolAttributes m
        , smtData = smtExtractor m constructors
        , sortConstructors = constructors
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
    SmtMetadataTools attributes -> Id -> Maybe Attribute.Constructors
findSortConstructors
    MetadataTools{sortConstructors}
    sortId =
        Map.lookup sortId sortConstructors
